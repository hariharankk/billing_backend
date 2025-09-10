from flask import Flask, request, jsonify, send_file
from flask_cors import CORS
from flask_sqlalchemy import SQLAlchemy
import datetime
from werkzeug.security import generate_password_hash, check_password_hash
import jwt
import logging
from functools import wraps
from pytz import timezone, utc
import io


class Config(object):
    SECRET_KEY= 'you-will-never-guess'

app = Flask(__name__)

# Set the SQLAlchemy database URI
app.config['SQLALCHEMY_DATABASE_URI'] = (
    'postgresql://doadmin:AVNS_El7-s7zchGaCFuyZeXQ@'
    'db-postgresql-nyc3-64138-do-user-17584761-0.f.db.ondigitalocean.com:25060/app'
    '?sslmode=require'
)

app.config.from_object(Config)
cors = CORS(app)
app.config['CORS_HEADERS'] = 'Content-Type'

db = SQLAlchemy(app)
IST = timezone('Asia/Kolkata')


def round_half_up(n):
    import math
    if n - math.floor(n) == 0.5:
        return math.ceil(n)
    else:
        return round(n)



def token_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        token = None
        # jwt is passed in the request header
        if 'x-access-token' in request.headers:
            app.logger.info('token present')
            token = request.headers['x-access-token']
        # return 401 if token is not passed
        if not token:
            app.logger.info('token not present')
            return jsonify({'message' : 'logged out'})

        try:
            # decoding the payload to fetch the stored details
            data = jwt.decode(token, app.config['SECRET_KEY'], algorithms=["HS256"])
            app.logger.info('getting user data')
            app.logger.info(data)
            current_user = User.query\
                .filter_by(username = data['public_id'])\
                .first()
        except:
            app.logger.info('exception')
            return jsonify({
               'message' : 'logged out'})
        # returns the current logged in users contex to the routes
        app.logger.info('success')
        return  f(current_user, *args, **kwargs)

    return decorated



def parse(string):
    d = {'True': True, 'False': False}
    return d.get(string, string)

user_products = db.Table('user_products',
    db.Column('user_id', db.Integer, db.ForeignKey('User.username'), primary_key=True),
    db.Column('product_id', db.Integer, db.ForeignKey('product.id'), primary_key=True)
)


class User(db.Model):
    __tablename__ = "User"
    username = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(80))
    email = db.Column(db.String(80), unique=True)
    password_hash = db.Column(db.String(256))
    admin=db.Column(db.Boolean, default=False, server_default="false")
    phonenumber=db.Column(db.String(80), unique=True)
    products = db.relationship('Product', secondary=user_products, backref='users')
    live_locations = db.relationship('LiveLocation', backref='user', lazy=True)
    transactions = db.relationship('Transaction', backref='user', lazy=True)


    @property
    def password(self):
        raise AttributeError('password is not a readable property')

    @password.setter
    def password(self, password):
        self.password_hash = generate_password_hash(password)

    def check_password(self, password):
        return check_password_hash(self.password_hash, password)

    @staticmethod
    def validate_email(email):
        if User.query.filter_by(email = email).first() is not None:
            return False
        else:
            return True


    def serialize_public(self):
        return {
            'name':self.name,
            'username': self.username,
            'emailaddress': self.email,
            'phonenumber': self.phonenumber,
            'admin':self.admin
        }



    def __repr__(self):
        return '<User {}>'.format(self.email)




@app.route('/login', methods=['GET', 'POST'])
def login():
    """Login Form"""
    if request.method == 'POST':
        try:
         user = User.query.filter_by(email=request.json['emailaddress']).first()
         print(user)
         print(request.json['password'])   
         print(user.check_password(request.json['password']))   
         if user is not None and user.check_password(request.json['password']):
                token = jwt.encode({
                    'public_id': user.username,
                }, app.config['SECRET_KEY'])
                app.logger.info('login sucessful')
                return jsonify({'status':True,'token':token.decode('utf-8'),'data':User.serialize_public(user)})
         else:
              app.logger.error('email method user name already exists')
              return jsonify({'status':False, 'message':'pass wrong'})
        except Exception as e:
            error_message = str(e)
            app.logger.error('Login function exception triggered')
            return jsonify({'status': False, 'message': error_message})
    else:
      return jsonify({'status':False, 'message':'post req'})


@app.route('/register/', methods=['POST'])
def register():
    """Register Form"""
    try:
        value_email = User.validate_email(request.json['emailaddress'])
        if value_email:
            new_user = User(
               email = request.json['emailaddress'],
               password = request.json['password'],
               name = request.json['name'],
               admin = parse(request.json['admin']),
               phonenumber = request.json['phonenumber']
               )
            db.session.add(new_user)
            db.session.commit()
            app.logger.info('registration success')
            return jsonify({'status':True,'data':User.serialize_public(new_user)})
        else:
          app.logger.error('registration data already exists')
          return jsonify({'status':False})
    except Exception as e:
      error_message = str(e)
      app.logger.error('registration function exception triggered')
      return jsonify({'status': False, 'message': error_message})


@app.route("/currentuser", methods=['GET'])
@token_required
def Current_user(user):
        app.logger.info('Current user acessed')
        return jsonify({'emailaddress':user.email,'admin':user.admin,'phonenumber':user.phonenumber,'username':user.username,'name':user.name})


class TransactionProduct(db.Model):
    __tablename__ = 'transaction_product'

    transaction_id = db.Column(db.Integer, db.ForeignKey('transaction.id'), primary_key=True)
    product_id = db.Column(db.Integer, db.ForeignKey('product.id'), primary_key=True)
    quantity = db.Column(db.Integer)

    # These fields store the product details at the time of transaction
    product_name_at_transaction = db.Column(db.String(100), nullable=False)
    product_description_at_transaction = db.Column(db.String(500), nullable=False)
    product_price_at_transaction = db.Column(db.Float, nullable=False)
    product_flatdiscount_at_transaction = db.Column(db.Float, nullable=False)
    product_weight_at_transaction = db.Column(db.Float, nullable=False)

    transaction = db.relationship("Transaction", backref=db.backref("transaction_products", cascade="all, delete-orphan"))
    product = db.relationship("Product", backref=db.backref("transaction_products", cascade="all, delete-orphan"))

class Product(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(100), nullable=False)
    description = db.Column(db.String(500), nullable=False)
    price = db.Column(db.Float, nullable=False)
    stock = db.Column(db.Integer, nullable=False)
    flatdiscount = db.Column(db.Float, nullable=False)
    weight = db.Column(db.Float, nullable=False)

    # Reference to the association table

    def __init__(self, id, name, description,  price ,stock, flatdiscount,weight):
        self.id = id
        self.name = name
        self.description = description
        self.price = price
        self.stock = stock
        self.flatdiscount = flatdiscount
        self.weight = weight


    def to_dict(self):
      return {
        'id': self.id,
        'name': self.name,
        'description': self.description,
        'price': self.price,
        'stock': self.stock,
        'flatdiscount':self.flatdiscount,
        'weight':self.weight
      }


@token_required
@app.route('/products/add', methods=['POST'])
def add_product():
    """
    Add a new product.
    """
    try:
        data = request.get_json()

        # Check if user exists
        user = User.query.get(data['userid'])
        if not user:
            app.logger.error('User not found: %s', data['userid'])
            return jsonify({'status': False, 'message': 'User not found'}), 404

        # Extract product data from request
        id = data['id']
        name = data['name']
        description = data['description']
        price = data['price']
        stock = data['stock']
        flatdiscount = data['flatdiscount']
        weight = data['weight']

        # Validate required fields
        if not all([id, name, description, price, stock, flatdiscount, weight]):
            app.logger.error('Missing or invalid parameters')
            return jsonify({'status': False, 'message': 'Missing or invalid parameters'}), 400

        # Create new product and associate with user
        new_product = Product(id=id, name=name, description=description, price=price, stock=stock, flatdiscount=flatdiscount, weight=weight)
        user.products.append(new_product)

        db.session.add(new_product)
        db.session.commit()
        app.logger.info('Product added successfully for user_id: %s', data['userid'])
        return jsonify({'status': True, 'product': new_product.to_dict()}), 201

    except Exception as e:
        app.logger.error('Error adding product: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/user/products', methods=['GET'])
def get_products_for_user():
    """
    Get all products for a user.
    """
    try:
        user_id = request.args.get('user_id', type=int)
        if not user_id:
            app.logger.error('Missing user_id')
            return jsonify({'status': False, 'message': 'Missing user_id'}), 400

        user = User.query.get(user_id)
        if not user:
            app.logger.error('User not found: %s', user_id)
            return jsonify({'status': False, 'message': 'User not found'}), 404

        app.logger.info('Products retrieved successfully for user_id: %s', user_id)
        return jsonify({'status': True, 'products': [product.to_dict() for product in user.products]}), 200

    except Exception as e:
        app.logger.error('Error retrieving products for user: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/user/products/getdata', methods=['GET'])
def get_product():
    """
    Get a specific product for a user.
    """
    try:
        user_id = request.args.get('user_id', type=int)
        product_id = request.args.get('product_id', type=int)

        if not user_id or not product_id:
            app.logger.error('Missing user_id or product_id parameter')
            return jsonify({'status': False, 'message': 'Missing user_id or product_id parameter'}), 400

        user = User.query.get(user_id)
        product = Product.query.get(product_id)

        if not user or not product or product not in user.products:
            app.logger.error('User or Product not found or not associated: user_id=%s, product_id=%s', user_id, product_id)
            return jsonify({'status': False, 'message': 'User or Product not found or not associated'}), 404

        app.logger.info('Product retrieved successfully: user_id=%s, product_id=%s', user_id, product_id)
        return jsonify({'status': True, 'product': product.to_dict()}), 200

    except Exception as e:
        app.logger.error('Error retrieving product: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/products/update', methods=['PATCH'])
def update_product():
    """
    Update an existing product.
    """
    try:
        user = User.query.get(request.args.get('userid'))
        product = Product.query.get(request.args.get('productid'))

        if not user or not product or product not in user.products:
            app.logger.error('User or Product not found or not associated: user_id=%s, product_id=%s', request.args.get('userid'), request.args.get('productid'))
            return jsonify({'status': False, 'message': 'User or Product not found or not associated'}), 404

        data = request.get_json()
        product.name = data.get('name', product.name)
        product.description = data.get('description', product.description)
        product.price = data.get('price', product.price)
        product.stock = data.get('stock', product.stock)
        product.flatdiscount = data.get('flatdiscount', product.flatdiscount)
        product.weight = data.get('weight', product.weight)

        db.session.commit()
        app.logger.info('Product updated successfully: user_id=%s, product_id=%s', request.args.get('userid'), request.args.get('productid'))
        return jsonify({'status': True, 'product': product.to_dict()}), 200

    except Exception as e:
        app.logger.error('Error updating product: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/user/products/delete', methods=['DELETE'])
def delete_product_for_user():
    """
    Delete a product for a user.
    """
    try:
        user_id = request.args.get('user_id', type=int)
        product_id = request.args.get('product_id', type=int)

        if not user_id or not product_id:
            app.logger.error('Missing user_id or product_id')
            return jsonify({'status': False, 'message': 'Missing user_id or product_id'}), 400

        user = User.query.get(user_id)
        product = Product.query.get(product_id)

        if not user or not product or product not in user.products:
            app.logger.error('User or Product not found or not associated: user_id=%s, product_id=%s', user_id, product_id)
            return jsonify({'status': False, 'message': 'User or Product not found or not associated'}), 404

        db.session.delete(product)
        db.session.commit()
        app.logger.info('Product deleted successfully: user_id=%s, product_id=%s', user_id, product_id)
        return jsonify({'status': True, 'message': 'Product deleted'}), 200

    except Exception as e:
        app.logger.error('Error deleting product: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

class Transaction(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey('User.username'), nullable=False)
    payment_method = db.Column(db.String(50), nullable=False)
    transaction_time = db.Column(db.DateTime(timezone=True), default=lambda: datetime.datetime.now(utc))
    lat = db.Column(db.String(128), nullable=False)
    longi = db.Column(db.String(128), nullable=False)
    customer_name = db.Column(db.String(255), nullable=True)
    customer_address = db.Column(db.String(255), nullable=True)
    customer_phone = db.Column(db.String(20), nullable=True)

    def __init__(self, user_id, payment_method, lat, longi, customer_name=None, customer_address=None, customer_phone=None):
        self.user_id = user_id
        self.payment_method = payment_method
        self.lat = lat
        self.longi = longi
        self.customer_name = customer_name
        self.customer_address = customer_address
        self.customer_phone = customer_phone

    def to_dict(self):
        transaction_dict = {
            'user_id': self.user_id,
            'id': self.id,
            'products': [
                {
                    'id': tp.product.id,
                    'name': tp.product_name_at_transaction,
                    'description': tp.product_description_at_transaction,
                    'price': tp.product_price_at_transaction,
                    'quantity': tp.quantity,
                    'flatdiscount': tp.product_flatdiscount_at_transaction,
                    'weight': tp.product_weight_at_transaction
                } for tp in self.transaction_products
            ],
            'transaction_time': self.transaction_time.astimezone(IST).strftime('%Y-%m-%dT%H:%M:%S'),
            'payment_method': self.payment_method,
            'lat': self.lat,
            'longi': self.longi,
            'total': float(
                round_half_up(sum((tp.product_price_at_transaction - tp.product_flatdiscount_at_transaction) * tp.quantity for tp in self.transaction_products))
            ),
        }

        if self.customer_name != None:
            transaction_dict['customer_name'] = self.customer_name
        if self.customer_address != None:
            transaction_dict['customer_address'] = self.customer_address
        if self.customer_phone != None:
            transaction_dict['customer_phone'] = self.customer_phone

        return transaction_dict
@token_required
@app.route('/transactions/all', methods=['GET'])
def get_transactions():
    """
    Get all transactions for a user for the current day based on IST.
    """
    try:
        user_id = request.args.get('user_id', type=int)
        if not user_id:
            app.logger.error('User ID not provided')
            return jsonify({'status': False, 'message': "User ID not provided"}), 400

        # Get current IST date
        now_ist = datetime.datetime.now(IST)
        today_start_ist = now_ist.replace(hour=0, minute=0, second=0, microsecond=0)
        today_end_ist = today_start_ist + datetime.timedelta(days=1)

        # Convert IST times to UTC for querying
        today_start_utc = today_start_ist.astimezone(utc)
        today_end_utc = today_end_ist.astimezone(utc)

        # Fetch transactions associated with the user from today in UTC
        transactions = Transaction.query \
            .filter(Transaction.user_id == user_id) \
            .filter(Transaction.transaction_time >= today_start_utc) \
            .filter(Transaction.transaction_time < today_end_utc) \
            .options(db.joinedload(Transaction.transaction_products)) \
            .order_by(Transaction.transaction_time.desc()) \
            .all()

        app.logger.info('Transactions retrieved successfully for user_id: %s', user_id)
        return jsonify({'status': True, 'transactions': [transaction.to_dict() for transaction in transactions]}), 200

    except Exception as e:
        app.logger.error('Error retrieving transactions: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/transactions/single', methods=['GET'])
def get_single_transaction():
    """
    Get a single transaction by transaction ID for a user.
    """
    try:
        transaction_id = request.args.get('transaction_id', type=int)
        user_id = request.args.get('user_id', type=int)

        if not transaction_id or not user_id:
            app.logger.error('Transaction ID or User ID not provided')
            return jsonify({'status': False, 'message': "Transaction ID or User ID not provided"}), 400

        transaction = Transaction.query \
            .filter(Transaction.id == transaction_id, Transaction.user_id == user_id) \
            .options(db.joinedload(Transaction.transaction_products)).first()

        if not transaction:
            app.logger.error('Transaction not found for transaction_id: %s and user_id: %s', transaction_id, user_id)
            return jsonify({'status': False, 'message': 'Transaction not found for the given user'}), 404

        app.logger.info('Transaction retrieved successfully: transaction_id=%s, user_id=%s', transaction_id, user_id)
        return jsonify({'status': True, 'transaction': transaction.to_dict()}), 200

    except Exception as e:
        app.logger.error('Error retrieving transaction: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/transactions/add', methods=['POST'])
def create_transaction():
    """
    Create a new transaction.
    """
    try:
        data = request.get_json()
        user_id = data['user_id']

        # Retrieve the user from the database
        user = User.query.get(user_id)
        if not user:
            app.logger.error('User not found: %s', user_id)
            return jsonify({'status': False, 'message': "User not found"}), 404

        # Extract the optional fields from the request data
        customer_name = data.get('customer_name', None)  # Optional field
        customer_address = data.get('customer_address', None)  # Optional field
        customer_phone = data.get('customer_phone', None)  # Optional field

        # Create the Transaction object with optional fields if provided
        new_transaction = Transaction(
            user_id=user_id,
            payment_method=data['payment_method'],
            lat=data['lat'],
            longi=data['longi'],
            customer_name=customer_name,  # Pass the customer_name if available
            customer_address=customer_address,  # Pass the customer_address if available
            customer_phone=customer_phone  # Pass the customer_phone if available
        )

        # Loop through the products and check availability
        for product_data in data['products']:
            product = Product.query.get(product_data['product_id'])
            if product is None:
                app.logger.error('Product not found: %s', product_data['product_id'])
                return jsonify({'status': False, 'message': f"Product with id {product_data['product_id']} not found"}), 400
            if product.stock < product_data['quantity']:
                app.logger.error('Not enough stock for product: %s', product.id)
                return jsonify({'status': False, 'message': f"Not enough of product {product.id} in stock"}), 400

        # Add the products to the transaction
        for product_data in data['products']:
            product = Product.query.get(product_data['product_id'])
            product.stock -= product_data['quantity']

            tp = TransactionProduct(
                transaction=new_transaction,
                product=product,
                quantity=product_data['quantity'],
                product_name_at_transaction=product.name,
                product_description_at_transaction=product.description,
                product_price_at_transaction=product.price,
                product_flatdiscount_at_transaction=product.flatdiscount,
                product_weight_at_transaction=product.weight
            )
            db.session.add(tp)

        # Commit the transaction to the database
        db.session.add(new_transaction)
        db.session.commit()
        app.logger.info('Transaction created successfully for user_id: %s', user_id)
        return jsonify({'status': True, 'transaction': new_transaction.to_dict()}), 201

    except Exception as e:
        app.logger.error('Error creating transaction: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/transactions/total_amount', methods=['GET'])
def get_total_amount():
    """
    Get total amounts for a user for the current day, including stock value, transaction totals, returns, and cash on hand.
    """
    try:
        user_id = request.args.get('user_id', type=int)
        if not user_id:
            app.logger.error('User ID not provided')
            return jsonify({'status': False, 'message': "User ID not provided"}), 400

        user = User.query.get(user_id)
        if not user:
            app.logger.error('User not found: %s', user_id)
            return jsonify({'status': False, 'message': "User not found"}), 404

        # Get products associated with the user and calculate total stock value
        products = user.products
        total_stock_value = round_half_up(sum([(product.price - product.flatdiscount) * product.stock for product in products]))

        # Format products for JSON response
        products_response = [product.to_dict() for product in products]  # Assuming to_dict() is defined for Product

        # Get current IST date
        now_ist = datetime.datetime.now(IST)
        today_start_ist = now_ist.replace(hour=0, minute=0, second=0, microsecond=0)
        today_end_ist = today_start_ist + datetime.timedelta(days=1)

        # Convert IST times to UTC for querying
        today_start_utc = today_start_ist.astimezone(utc)
        today_end_utc = today_end_ist.astimezone(utc)

        # Get all transactions for today in UTC for the specific user
        transactions = Transaction.query \
            .filter(Transaction.user_id == user_id) \
            .filter(Transaction.transaction_time >= today_start_utc) \
            .filter(Transaction.transaction_time < today_end_utc) \
            .options(db.joinedload(Transaction.transaction_products)) \
            .all()

        returns = ReturnTable.query \
            .filter(ReturnTable.user_id == user_id) \
            .filter(ReturnTable.transaction_time >= today_start_utc) \
            .filter(ReturnTable.transaction_time < today_end_utc) \
            .all()
        # Fuel value tracking removed
        fuel_value_today = 0.0

        total_return_amount = 0

        for return_entry in returns:
            total_return_amount += return_entry.price

        cash_total = 0
        upi_total = 0

        # Calculate total for each transaction using the saved price and discount
        for transaction in transactions:
            transaction_total = round_half_up(sum([
                (tp.product_price_at_transaction - tp.product_flatdiscount_at_transaction)
                * tp.quantity for tp in transaction.transaction_products]))

            # Add the transaction total to the appropriate payment method total
            if transaction.payment_method == 'cash':
                cash_total += transaction_total
            elif transaction.payment_method == 'upi':
                upi_total += transaction_total

        Commision = float(round_half_up((cash_total + upi_total - total_return_amount) * 0.0025))
        cash_on_hand = round_half_up(cash_total - (total_return_amount))

        app.logger.info('Total amounts calculated successfully for user_id: %s', user_id)
        return {
            'products': products_response,
            'total_stock_value': total_stock_value,
            'cash_total': float(round_half_up(cash_total)),
            'upi_total': float(round_half_up(upi_total)),
            'total_return_amount': float(round_half_up(total_return_amount)),
            'commission': Commision,
            'fuel_value_today': fuel_value_today,
            'cash_on_hand': cash_on_hand,
        }, 200

    except Exception as e:
        app.logger.error('Error calculating total amounts: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

class LiveLocation(db.Model):
    __tablename__ = "LiveLocation"
    location_key = db.Column(db.Integer, primary_key=True, unique=True, autoincrement=True)
    user_id = db.Column(db.Integer, db.ForeignKey('User.username'), nullable=False)  # Assuming 'username' is the primary key of the User model
    lat = db.Column(db.String(128))
    longi = db.Column(db.String(128))
    time_created = db.Column(db.DateTime(timezone=True), default=lambda: datetime.datetime.now(utc))

    def __init__(self, lat ,longi,user_id):
        self.longi = longi
        self.lat = lat
        self.user_id = user_id


    def serialize(self):
        return {
            'user_id': self.user_id,
            'location_key': self.location_key,
            'longi': self.longi,
            'lat': self.lat,
            'time': self.time_created.astimezone(IST).strftime('%Y-%m-%dT%H:%M:%S')  # Convert to IST
        }
@token_required
@app.route('/api/location-add', methods=['POST'])
def add_location():
    """
    Add a new location entry for a user.
    """
    try:
        json_data = request.get_json(force=True)

        # Get user by ID and check if they exist
        user = User.query.get(json_data['userid'])
        if not user:
            app.logger.error('User not found: %s', json_data['userid'])
            return {"status": 'fail', 'message': 'User not found'}, 404

        # Create new location associated with the user
        location = LiveLocation(
            lat=json_data['lat'],
            longi=json_data['longi'],
            user_id=json_data['userid']  # Assuming 'username' is the primary key of the User model
        )

        db.session.add(location)
        db.session.commit()

        result = location.serialize()
        app.logger.info('Location added successfully for user_id: %s', json_data['userid'])

        return {"status": True, 'data': result}, 200

    except Exception as e:
        app.logger.error('Error adding location: %s', str(e))
        return {"status": False, 'message': str(e)}, 500

@token_required
@app.route('/api/location-get', methods=['GET'])
def get_location():
    """
    Get location entries for a user for the current day.
    """
    try:
        result = []
        user = User.query.get(request.args.get('userid'))
        if not user:
            app.logger.error('User not found: %s', request.args.get('userid'))
            return {"status": 'fail', 'message': 'User not found'}, 404

        # Get the current date in IST
        now_ist = datetime.datetime.now(IST)
        today_start_ist = now_ist.replace(hour=0, minute=0, second=0, microsecond=0)
        today_end_ist = today_start_ist + datetime.timedelta(days=1)

        # Convert IST times to UTC for querying
        today_start_utc = today_start_ist.astimezone(utc)
        today_end_utc = today_end_ist.astimezone(utc)

        # Fetch locations associated with the user from today in UTC
        locations = LiveLocation.query.filter(
            LiveLocation.user_id == user.username,
            LiveLocation.time_created >= today_start_utc,
            LiveLocation.time_created < today_end_utc
        ).order_by(LiveLocation.time_created.desc()).all()

        if locations:
            for loc in locations:
                result.append(loc.serialize())

            app.logger.info('Locations retrieved successfully for user_id: %s', request.args.get('userid'))
            return {"status": True, 'data': result}, 200
        else:
            app.logger.warning('No locations found for user_id: %s', request.args.get('userid'))
            return {"status": False, 'message': "Locations Not Found"}, 404

    except Exception as e:
        app.logger.error('Error retrieving locations: %s', str(e))
        return {"status": False, 'message': str(e)}, 500



class Images(db.Model):
    __tablename__ = "Images"
    id = db.Column(db.Integer,primary_key=True)
    name = db.Column(db.String(128), nullable=False)
    img = db.Column(db.LargeBinary)

@token_required
@app.route('/deletefile/<string:name>', methods=['GET'])
def delete_file(name):
    """
    Delete an image file by name.
    """
    try:
        obj = Images.query.filter_by(name=name).first()
        if obj is None:
            app.logger.error('File not found: %s', name)
            return jsonify({'status': False, 'message': 'File not found'}), 404

        db.session.delete(obj)
        db.session.commit()
        app.logger.info('File deleted successfully: %s', name)
        return jsonify({'status': True, 'message': 'File deleted successfully'})
    except Exception as e:
        app.logger.error('Error deleting file: %s', str(e))
        return jsonify({'status': False, 'message': 'Error deleting file'}), 500

@token_required
@app.route('/image/<string:filename>', methods=['GET'])
def download_image(filename):
    """
    Download an image by filename.
    """
    try:
        image = Images.query.filter_by(name=filename).first()
        if image is None or not image.img:
            app.logger.error('Image not found or no data: %s', filename)
            return jsonify({'status': False, 'message': 'Image not found or no data'}), 404

        app.logger.info('Image retrieved successfully: %s', filename)
        return send_file(
            io.BytesIO(image.img),
            as_attachment=False,
            mimetype='image/png'
        )
    except Exception as e:
        app.logger.error('Error retrieving image: %s', str(e))
        return jsonify({'status': False, 'message': 'Error retrieving image'}), 500

@token_required
@app.route('/img-profile', methods=['POST'])
def upload_profile():
    """
    Upload a profile image.
    """
    try:
        file = request.files['file']
        data = file.read()
        new_file = Images(name=file.filename, img=data)
        db.session.add(new_file)
        db.session.commit()
        app.logger.info('File uploaded successfully: %s', file.filename)
        return jsonify({'status': True, 'file_name': file.filename})
    except Exception as e:
        app.logger.error('Error uploading file: %s', str(e))
        return jsonify({'status': False, 'message': 'Error uploading file'}), 500


class ReturnTable(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey('User.username'), nullable=False)  # <-- Add this line
    imgurl = db.Column(db.String(255), nullable=False)
    reason = db.Column(db.String(255), nullable=False)
    transaction_time = db.Column(db.DateTime(timezone=True), default=lambda: datetime.datetime.now(utc))
    lat = db.Column(db.String(128), nullable=False)
    longi = db.Column(db.String(128), nullable=False)
    name = db.Column(db.String(100), nullable=False)
    description = db.Column(db.String(500), nullable=False)
    price = db.Column(db.Float, nullable=False)
    returnquantity = db.Column(db.Float, nullable=False)
    quantity = db.Column(db.Float, nullable=False)
    trans_id = db.Column(db.Integer, nullable=False)
    idurl = db.Column(db.String(255), nullable=False)


    def __init__(self, user_id, imgurl, lat, longi, name ,description, price, quantity,returnquantity,reason,idurl,trans_id):  # <-- Update the constructor
        self.user_id = user_id
        self.imgurl = imgurl
        self.lat = lat
        self.longi = longi
        self.name = name
        self.description = description
        self.price = price
        self.quantity = quantity
        self.returnquantity = returnquantity
        self.reason = reason
        self.idurl = idurl
        self.trans_id = trans_id

    def serialize(self):
        return {
          'id': self.id,
          'user_id': self.user_id,
          'name': self.name,
          'description': self.description,
          'price': self.price,
          'returnquantity': self.returnquantity,
          'quantity': self.quantity,
          'imgurl': self.imgurl,
          'transaction_time':self.transaction_time.astimezone(IST).strftime('%Y-%m-%dT%H:%M:%S'),
          'lat': self.lat,
          'long': self.longi,
          'reason' : self.reason,
          'idurl':self.idurl,
          'trans_id':self.trans_id
        }

@token_required
@app.route('/returns/add', methods=['POST'])
def add_return():
    try:
        data = request.get_json()
        user_id = data.get('user_id')
        user = User.query.get(user_id)

        if not user:
            app.logger.error('User not found for user_id %s', user_id)
            return jsonify({'status': False, 'message': 'User not found'}), 404

        imgurl = data.get('imgurl')
        lat = data.get('lat')
        longi = data.get('longi')
        name = data.get('name')
        description = data.get('description')
        price = data.get('price')
        quantity = data.get('quantity')
        returnquantity = data.get('returnquantity')
        reason = data.get('reason')
        idurl = data.get('idurl')
        trans_id = data.get('trans_id')



        # Check for missing or invalid parameters
        if not all([user_id, imgurl,  lat, longi, name, description, price, returnquantity, reason, idurl, trans_id]):
            app.logger.error('Missing or invalid parameters')
            return jsonify({'status': False, 'message': 'Missing or invalid parameters'}), 400

        new_return = ReturnTable(
            user_id=user_id,
            imgurl=imgurl,
            lat=lat,
            longi=longi,
            name=name,
            description=description,
            price=price,
            quantity=quantity,
            returnquantity=returnquantity,
            reason=reason,
            idurl=idurl,
            trans_id=trans_id
        )

        db.session.add(new_return)
        db.session.commit()
        app.logger.info('Return entry created successfully for user_id %s', user_id)
        return jsonify({'status': True, 'return_data': new_return.serialize()}), 201

    except Exception as e:
        app.logger.error('Error creating return entry: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/returns/get', methods=['GET'])
def get_returns():
    try:
        user_id = request.args.get('user_id')
        if not user_id:
            app.logger.error('User ID not provided')
            return jsonify({'status': False, 'message': 'User ID not provided'}), 400

        user = User.query.get(user_id)
        if not user:
            app.logger.error('User not found for user_id %s', user_id)
            return jsonify({'status': False, 'message': 'User not found'}), 404

        return_data = ReturnTable.query.filter_by(user_id=user_id).all()
        app.logger.info('Return entries retrieved successfully for user_id %s', user_id)
        return jsonify({'status': True, 'return_data': [rd.serialize() for rd in return_data]}), 200

    except Exception as e:
        app.logger.error('Error retrieving return entries: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500


class ShopData(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey('User.username'), nullable=False)  # <-- Add this line
    imgurl = db.Column(db.String(255), nullable=False)
    feedback = db.Column(db.String(255), nullable=False)
    lat = db.Column(db.String(128), nullable=False)
    longi = db.Column(db.String(128), nullable=False)
    name = db.Column(db.String(100), nullable=False)
    description = db.Column(db.String(500), nullable=False)
    Limit = db.Column(db.Float, nullable=False)
    rating = db.Column(db.Float, nullable=False)


    def __init__(self, user_id, imgurl, lat, longi, name ,description, Limit, rating ,feedback):  # <-- Update the constructor
        self.user_id = user_id
        self.imgurl = imgurl
        self.lat = lat
        self.longi = longi
        self.name = name
        self.description = description
        self.Limit = Limit
        self.rating = rating
        self.feedback = feedback

    def serialize(self):
        return {
          'id': self.id,
          'user_id': self.user_id,
          'name': self.name,
          'description': self.description,
          'Limit': self.Limit,
          'rating': self.rating,
          'feedback': self.feedback,
          'imgurl': self.imgurl,
          'lat': self.lat,
          'long': self.longi,
        }

@token_required
@app.route('/shopdata/add', methods=['POST'])
def add_shop():
    try:
        data = request.get_json()
        user_id = data.get('user_id')
        user = User.query.get(user_id)

        if not user:
            app.logger.error('User not found for user_id %s', user_id)
            return jsonify({'status': False, 'message': 'User not found'}), 404

        imgurl = data.get('imgurl')
        lat = data.get('lat')
        longi = data.get('longi')
        name = data.get('name')
        description = data.get('description')
        Limit = data.get('Limit')
        rating = data.get('rating')
        feedback = data.get('feedback')



        # Check for missing or invalid parameters
        if not all([user_id, imgurl,  lat, longi, name, description, Limit, rating, feedback]):
            app.logger.error('Missing or invalid parameters')
            return jsonify({'status': False, 'message': 'Missing or invalid parameters'}), 400

        new_shop = ShopData(
            user_id=user_id,
            imgurl=imgurl,
            lat=lat,
            longi=longi,
            name=name,
            Limit=Limit,
            rating=rating,
            feedback=feedback,
            description=description,
        )

        db.session.add(new_shop)
        db.session.commit()
        app.logger.info('New Shop sucessfully added by user_id %s', user_id)
        return jsonify({'status': True, 'shop_data': new_shop.serialize()}), 201

    except Exception as e:
        app.logger.error('Error creating shop data: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/shopdata/get', methods=['GET'])
def get_shops():
    try:
        user_id = request.args.get('user_id')
        if not user_id:
            app.logger.error('User ID not provided')
            return jsonify({'status': False, 'message': 'User ID not provided'}), 400

        user = User.query.get(user_id)
        if not user:
            app.logger.error('User not found for user_id %s', user_id)
            return jsonify({'status': False, 'message': 'User not found'}), 404

        shop_data = ShopData.query.filter_by(user_id=user_id).all()
        app.logger.info('shop data retrieved successfully for user_id %s', user_id)
        return jsonify({'status': True, 'shop_data': [sd.serialize() for sd in shop_data]}), 200

    except Exception as e:
        app.logger.error('Error retrieving shop data: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500



if __name__ == '__main__':
  with app.app_context():
    logging.basicConfig(filename='error.log',level=logging.INFO)
    db.create_all()
  app.run(port=5001)

from shapely import wkb, wkt
from flask import Flask, request, jsonify, send_file,after_this_request,session
from flask_cors import CORS, cross_origin
from flask_sqlalchemy import SQLAlchemy
import requests
import datetime
import random
import string
from datetime import timedelta
import numpy as np
import os
from werkzeug.security import generate_password_hash, check_password_hash
import jwt
import random
import string
import logging
from functools import wraps
import json
from pytz import timezone, utc
import io
from sqlalchemy import and_ , func, event
from geoalchemy2 import Geometry , WKTElement
import itertools
import networkx as nx
from math import radians, sin, cos, sqrt, atan2
from shapely.wkb import loads
from geoalchemy2.shape import to_shape
import math


#from pyngrok import ngrok  #NGROK not need

# Set your ngrok authtoken
#ngrok.set_auth_token("2NKKGX1X7To9Tbi4ab0wIYvyfsP_63PSNHUNtJ8HXdPoqktt5") #NGROK not need

#public_url = ngrok.connect(5001)  # Change to a different port #NGROK not need
#print(f"ngrok tunnel \"{public_url}\" -> \"http://localhost:5001\"")  #NGROK not need


class Config(object):
    SECRET_KEY= 'you-will-never-guess'

app = Flask(__name__)
# Get the current working directory (cwd) of the application
basedir = os.path.abspath(os.path.dirname(__file__))

# Construct the path to the SQLite database file in the application directory
db_path = os.path.join(basedir, 'image5.db')

# Set the SQLAlchemy database URI
app.config['SQLALCHEMY_DATABASE_URI'] = f'sqlite:///{db_path}'
app.config.from_object(Config)
cors = CORS(app)
app.config['CORS_HEADERS'] = 'Content-Type'

db = SQLAlchemy(app)
IST = timezone('Asia/Kolkata')

def load_spatialite(dbapi_conn, connection_record):
  # From https://geoalchemy-2.readthedocs.io/en/latest/spatialite_tutorial.html
  dbapi_conn.enable_load_extension(True)
  dbapi_conn.load_extension('/usr/lib/x86_64-linux-gnu/mod_spatialite.so')



def round_half_up(n):
    import math
    if n - math.floor(n) == 0.5:
        return math.ceil(n)
    else:
        return round(n)


def calculate_initial_compass_bearing(pointA, pointB):
    """
    Calculates the bearing between two points.

    The formulae used is the following:
        θ = atan2(sin(Δlong).cos(lat2),
                  cos(lat1).sin(lat2) − sin(lat1).cos(lat2).cos(Δlong))

    :param pointA: tuple of (latitude, longitude) of the start point
    :param pointB: tuple of (latitude, longitude) of the end point
    :returns: bearing as a float, degrees from north
    """
    if (type(pointA) != tuple) or (type(pointB) != tuple):
        raise TypeError("Only tuples are supported as arguments")

    lat1 = math.radians(pointA[0])
    lat2 = math.radians(pointB[0])

    diffLong = math.radians(pointB[1] - pointA[1])

    x = math.sin(diffLong) * math.cos(lat2)
    y = math.cos(lat1) * math.sin(lat2) - (math.sin(lat1) * math.cos(lat2) * math.cos(diffLong))

    initial_bearing = math.atan2(x, y)

    # Now we have the initial bearing but math.atan2 return values
    # from -π to +π which is not what we want for a compass bearing
    # The solution is to normalize the initial bearing as shown below
    initial_bearing = math.degrees(initial_bearing)
    bearing = (initial_bearing + 360) % 360

    return bearing


def haversine_distance(coord1, coord2):
    R = 6371  # Radius of the Earth in kilometers

    lat1, lon1 = radians(coord1[1]), radians(coord1[0])
    lat2, lon2 = radians(coord2[1]), radians(coord2[0])

    dlat = lat2 - lat1
    dlon = lon2 - lon1

    a = sin(dlat/2)**2 + cos(lat1) * cos(lat2) * sin(dlon/2)**2
    c = 2 * atan2(sqrt(a), sqrt(1-a))

    return R * c  # distance in kilometers

# Create a function to find nodes with odd degrees in the graph
def find_odd_degree_nodes(graph):
    odd_degree_nodes = [v for v, d in graph.degree() if d % 2 == 1]
    return odd_degree_nodes

# Create a function to compute the shortest paths and store them with distances
def get_shortest_paths_distances(graph, pairs):
    distances = {}
    for pair in pairs:
        distances[pair] = nx.dijkstra_path_length(graph, pair[0], pair[1])
    return distances



def create_eulerian_circuit(graph_augmented, graph_original, starting_node=None):
    """Create the eulerian path using only edges from the original graph."""
    euler_circuit = []
    naive_circuit = list(nx.eulerian_path(graph_augmented, source=starting_node))

    for edge in naive_circuit:
        edge_data = graph_augmented.get_edge_data(edge[0], edge[1])

        if edge_data[0]['trail'] != 'augmented':
            # If `edge` exists in original graph, grab the edge attributes and add to eulerian circuit.
            edge_att = graph_original[edge[0]][edge[1]]
            euler_circuit.append((edge[0], edge[1], edge_att))
        else:
            aug_path = nx.shortest_path(graph_original, edge[0], edge[1], weight='distance')
            aug_path_pairs = list(zip(aug_path[:-1], aug_path[1:]))

            print('Filling in edges for augmented edge: {}'.format(edge))
            print('Augmenting path: {}'.format(' => '.join(["({}, {})".format(x, y) for (x, y) in aug_path])))
            print('Augmenting path pairs: {}\n'.format(aug_path_pairs))

            # If `edge` does not exist in original graph, find the shortest path between its nodes and
            #  add the edge attributes for each link in the shortest path.
            for edge_aug in aug_path_pairs:
                edge_aug_att = graph_original[edge_aug[0]][edge_aug[1]]
                euler_circuit.append((edge_aug[0], edge_aug[1], edge_aug_att))

    return euler_circuit

def remove_immediate_retracing(euler_circuit, graph):
    """Remove immediate retracing of edges from the Eulerian circuit, considering node degrees."""
    optimized_circuit = []
    skip_count = 0

    i = 0
    while i < len(euler_circuit) - 1:
        if skip_count > 0:
            skip_count -= 1
            i += 1
            continue

        node1 = euler_circuit[i][0]
        node2 = euler_circuit[i][1]
        next_node1 = euler_circuit[i + 1][0]
        next_node2 = euler_circuit[i + 1][1]

        if (node1 == next_node2 and node2 == next_node1):
            # Check the degrees of the nodes
            if graph.degree[node1] > 1 and graph.degree[node2] > 1:
                # Skip both the current edge and the next edge (remove both the initial crossing and the retracing)
                skip_count = 1
            else:
                # Add the current edge as it should not be removed
                optimized_circuit.append(euler_circuit[i])
        else:
            # Add the current edge as it's not a retracing
            optimized_circuit.append(euler_circuit[i])

        i += 1

    # Append the last edge if it was not skipped
    if skip_count == 0:
        optimized_circuit.append(euler_circuit[-1])

    return optimized_circuit


# Create a function to create a complete graph
def create_complete_graph(pair_weights, flip_weights=True):
    g = nx.Graph()
    for k, v in pair_weights.items():
        wt_i = -v if flip_weights else v
        g.add_edge(k[0], k[1], distance=v, weight=wt_i)
    return g

# Add augmenting path to graph
def add_augmenting_path_to_graph(graph, min_weight_pairs):
    graph_aug = nx.MultiGraph(graph.copy())
    for pair in min_weight_pairs:
        graph_aug.add_edge(pair[0], pair[1], distance=nx.dijkstra_path_length(graph, pair[0], pair[1]), trail='augmented')
    return graph_aug


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
    password_hash = db.Column(db.String(128))
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

    @staticmethod
    def validate_user_name(username):
        if User.query.filter_by(username = username).first() is not None:
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
         if user is not None and user.check_password(request.json['password']):
                token = jwt.encode({
                    'public_id': user.username,
                }, app.config['SECRET_KEY'])
                app.logger.info('login sucessful')
                return jsonify({'status':True,'token':token.decode('utf-8'),'data':User.serialize_public(user)})
         else:
              app.logger.error('email method user name already exists')
              return jsonify({'status':False})
        except Exception as e:
            error_message = str(e)
            app.logger.error('Login function exception triggered')
            return jsonify({'status': False, 'message': error_message})
    else:
      return jsonify({'status':False})


@app.route('/register/', methods=['POST'])
def register():
    """Register Form"""
    try:
      if request.method == 'POST':
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
      else:
          app.logger.error('registration wrong request')
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
    user_id = db.Column(db.Integer, db.ForeignKey('User.username'), nullable=False)  # <-- Add this line
    payment_method = db.Column(db.String(50), nullable=False)
    transaction_time = db.Column(db.DateTime(timezone=True), default=lambda: datetime.datetime.now(utc))
    lat = db.Column(db.String(128), nullable=False)
    longi = db.Column(db.String(128), nullable=False)

    def __init__(self, user_id, payment_method, lat, longi):  # <-- Update the constructor
        self.user_id = user_id
        self.payment_method = payment_method
        self.lat = lat
        self.longi = longi

    def to_dict(self):
        return {
            'user_id': self.user_id,
            'id': self.id,
            'products': [
                {
                    'id': tp.product.id,
                    'name': tp.product_name_at_transaction,  # Taken from TransactionProduct's stored data
                    'description': tp.product_description_at_transaction,  # Taken from TransactionProduct's stored data
                    'price': tp.product_price_at_transaction,  # Taken from TransactionProduct's stored data
                    'quantity': tp.quantity,
                    'flatdiscount': tp.product_flatdiscount_at_transaction,  # Taken from TransactionProduct's stored data
                    'weight': tp.product_weight_at_transaction  # New addition here
                } for tp in self.transaction_products
            ],
            'transaction_time': self.transaction_time.astimezone(IST).strftime('%Y-%m-%dT%H:%M:%S'),
            'payment_method': self.payment_method,
            'lat': self.lat,
            'longi': self.longi,
            'total': float(round_half_up(
                sum((tp.product_price_at_transaction - tp.product_flatdiscount_at_transaction) * tp.quantity for tp in self.transaction_products)
                + (sum((tp.product_price_at_transaction - tp.product_flatdiscount_at_transaction) * tp.quantity for tp in self.transaction_products) * 0.05)
            )),
        }


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

        user = User.query.get(user_id)
        if not user:
            app.logger.error('User not found: %s', user_id)
            return jsonify({'status': False, 'message': "User not found"}), 404

        new_transaction = Transaction(user_id=user_id, payment_method=data['payment_method'], lat=data['lat'], longi=data['longi'])

        for product_data in data['products']:
            product = Product.query.get(product_data['product_id'])
            if product is None:
                app.logger.error('Product not found: %s', product_data['product_id'])
                return jsonify({'status': False, 'message': f"Product with id {product_data['product_id']} not found"}), 400
            if product.stock < product_data['quantity']:
                app.logger.error('Not enough stock for product: %s', product.id)
                return jsonify({'status': False, 'message': f"Not enough of product {product.id} in stock"}), 400

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
        total_stock_value = round_half_up(sum([(product.price - product.flatdiscount) * product.stock for product in products]) + (sum([(product.price - product.flatdiscount) * product.stock for product in products]) * 0.05))

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


        logbook_entry = Logbook.query.filter(and_(Logbook.user_id == user_id, Logbook.time_created >= today_start_utc, Logbook.time_created < today_end_utc)).first()
        # Calculate the fuel value for today
        fuel_value_today = 0.0  # default value
        if logbook_entry:
            fuel_value_today = float(round_half_up(logbook_entry.fuel_filled_litres * logbook_entry.cost_per_litre))

        total_return_amount = 0

        for return_entry in returns:
            total_return_amount += return_entry.price

        cash_total = 0
        upi_total = 0

        # Calculate total for each transaction using the saved price and discount
        for transaction in transactions:
            transaction_total = round_half_up(sum([(tp.product_price_at_transaction - tp.product_flatdiscount_at_transaction) * tp.quantity for tp in transaction.transaction_products]) + (sum([(tp.product_price_at_transaction - tp.product_flatdiscount_at_transaction) * tp.quantity for tp in transaction.transaction_products]) * 0.05))

            # Add the transaction total to the appropriate payment method total
            if transaction.payment_method == 'cash':
                cash_total += transaction_total
            elif transaction.payment_method == 'upi':
                upi_total += transaction_total

        Commision = float(round_half_up((cash_total + upi_total - total_return_amount) * 0.01))
        cash_on_hand = round_half_up(cash_total - (total_return_amount + fuel_value_today), )

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
    if request.method == 'GET':
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
    else:
        return jsonify({'status': False, 'message': 'Invalid request method'}), 405

@token_required
@app.route('/image/<string:filename>', methods=['GET'])
def download_image(filename):
    """
    Download an image by filename.
    """
    if request.method == 'GET':
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
    else:
        return jsonify({'status': False, 'message': 'Invalid request method'}), 405

@token_required
@app.route('/img-profile', methods=['POST'])
def upload_profile():
    """
    Upload a profile image.
    """
    if request.method == 'POST':
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
    else:
        return jsonify({'status': False, 'message': 'Invalid request method'}), 405


class ReturnTable(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey('User.username'), nullable=False)  # <-- Add this line
    imgurl = db.Column(db.String(50), nullable=False)
    reason = db.Column(db.String(50), nullable=False)
    transaction_time = db.Column(db.DateTime(timezone=True), default=lambda: datetime.datetime.now(utc))
    lat = db.Column(db.String(128), nullable=False)
    longi = db.Column(db.String(128), nullable=False)
    name = db.Column(db.String(100), nullable=False)
    description = db.Column(db.String(500), nullable=False)
    price = db.Column(db.Float, nullable=False)
    returnquantity = db.Column(db.Float, nullable=False)
    quantity = db.Column(db.Float, nullable=False)
    trans_id = db.Column(db.Integer, nullable=False)
    idurl = db.Column(db.String(50), nullable=False)


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



def current_ist_date():
    return datetime.datetime.now(IST).date()

class Logbook(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey('User.username'), nullable=False)
    date = db.Column(db.DateTime, nullable=False, default=current_ist_date, unique=True)
    time_created = db.Column(db.DateTime(timezone=True), default=lambda: datetime.datetime.now(utc))
    morning_km = db.Column(db.Float, default=0.0)
    night_km = db.Column(db.Float, default=0.0)
    fuel_filled_litres = db.Column(db.Float, default=0.0)
    cost_per_litre = db.Column(db.Float, default=0.0)
    fuel_start_km = db.Column(db.Float, default=0.0)
    fuelurl = db.Column(db.String(50), default='')
    fueltime = db.Column(db.Time, nullable=True)
    morningtime = db.Column(db.Time, nullable=True)
    nighttime = db.Column(db.Time, nullable=True)
    morningurl = db.Column(db.String(50), default='')
    nighturl = db.Column(db.String(50), default='')
    fuel_updated = db.Column(db.Boolean, default=False)  # <-- Add this line
    night_km_updated = db.Column(db.Boolean, default=False)  # <-- Add this line

    def __init__(self, user_id, morning_km, morningurl, night_km=None, fuel_filled_litres=None, cost_per_litre=None, fuel_start_km=None, fuelurl=None, nighturl=None, morningtime=None, nighttime=None, fueltime=None):
        self.user_id = user_id
        self.morning_km = morning_km
        self.night_km = night_km
        self.fuel_filled_litres = fuel_filled_litres
        self.cost_per_litre = cost_per_litre
        self.fuel_start_km = fuel_start_km
        self.fuelurl = fuelurl
        self.morningurl = morningurl
        self.nighturl = nighturl
        self.morningtime = morningtime
        self.nighttime = nighttime
        self.fueltime = fueltime
        self.fuel_updated = False
        self.night_km_updated = False

    def serialize(self):
        return {
            'date': self.time_created.astimezone(IST).strftime('%Y-%m-%dT%H:%M:%S'),
            'id': self.id,
            'user_id': self.user_id,
            'morning_km': self.morning_km,
            'night_km': self.night_km,
            'fuel_filled_litres': self.fuel_filled_litres,
            'cost_per_litre': self.cost_per_litre,
            'fuel_start_km': self.fuel_start_km,
            'fuelurl': self.fuelurl,
            'morningurl': self.morningurl,
            'nighturl': self.nighturl,
            'fueltime': str(self.fueltime) if self.fueltime else None,
            'morningtime': str(self.morningtime) if self.morningtime else None,
            'nighttime': str(self.nighttime) if self.nighttime else None,
            'fuel_updated': self.fuel_updated,
            'night_km_updated': self.night_km_updated
        }

# Helper function to get today's logbook entry for a user
def get_today_logbook_entry(user_id):
    ist_now = datetime.datetime.now(IST)
    start_of_day = ist_now.replace(hour=0, minute=0, second=0, microsecond=0)
    end_of_day = start_of_day + datetime.timedelta(days=1)
    start_of_day_utc = start_of_day.astimezone(utc)
    end_of_day_utc = end_of_day.astimezone(utc)
    return Logbook.query.filter(
        and_(Logbook.user_id == user_id, Logbook.time_created >= start_of_day_utc, Logbook.time_created <= end_of_day_utc)
    ).first()

@token_required
@app.route('/user/logbook/create', methods=['POST'])
def create_entry_for_user():
    data = request.get_json()
    user_id = int(data.get('user_id'))
    morning_km = data.get('morning_km')
    morningurl = data.get('morningurl')
    morningtime = datetime.datetime.now(IST).time()

    if not morning_km or not morningurl:
        app.logger.error('Missing vehicle_id, date, or morning_km')
        return jsonify({'status': False, 'message': 'Missing vehicle_id, date, or morning_km'}), 400

    try:
        new_entry = Logbook(user_id=user_id, morning_km=morning_km, morningurl=morningurl, morningtime=morningtime)
        db.session.add(new_entry)
        db.session.commit()
        app.logger.info('Logbook entry created successfully for user_id %s', user_id)
        return jsonify({'status': True, 'message': 'Entry created successfully', 'id': new_entry.id}), 201
    except Exception as e:
        app.logger.error('Error creating logbook entry: %s', str(e))
        return jsonify({'status': False, 'message': 'Error creating logbook entry'}), 500

@token_required
@app.route('/user/logbook/update_fuel', methods=['PATCH'])
def update_fuel_for_user():
    data = request.get_json()
    user_id = int(data.get('user_id'))
    fuel_filled_litres = data.get('fuel_filled_litres')
    cost_per_litre = data.get('cost_per_litre')
    fuel_start_km = data.get('fuel_start_km')
    fuelurl = data.get('fuelurl')
    fueltime = datetime.datetime.now(IST).time()

    if not fuel_filled_litres or not cost_per_litre or not fuel_start_km or not fuelurl:
        app.logger.error('Missing fuel details')
        return jsonify({'status': False, 'message': 'Missing fuel details'}), 400

    try:
        logbook_entry = get_today_logbook_entry(user_id)
        if not logbook_entry:
            app.logger.error('Logbook entry not found for user_id %s', user_id)
            return jsonify({'status': False, 'message': 'Logbook entry not found'}), 404

        if logbook_entry.fuel_updated:
            app.logger.error('Fuel details already updated for user_id %s', user_id)
            return jsonify({'status': False, 'message': 'Fuel details already updated for today'}), 400

        logbook_entry.fuel_filled_litres = fuel_filled_litres
        logbook_entry.cost_per_litre = cost_per_litre
        logbook_entry.fuel_start_km = fuel_start_km
        logbook_entry.fuelurl = fuelurl
        logbook_entry.fueltime = fueltime
        logbook_entry.fuel_updated = True
        db.session.commit()
        app.logger.info('Fuel details updated successfully for user_id %s', user_id)
        return jsonify({'status': True, 'message': 'Fuel details updated successfully'}), 200
    except Exception as e:
        app.logger.error('Error updating fuel details: %s', str(e))
        return jsonify({'status': False, 'message': 'Error updating fuel details'}), 500

@token_required
@app.route('/user/logbook/update_night_km', methods=['PATCH'])
def update_night_km_for_user():
    data = request.get_json()
    user_id = int(data.get('user_id'))
    night_km = data.get('night_km')
    nighturl = data.get('nighturl')
    nighttime = datetime.datetime.now(IST).time()

    if not night_km or not nighturl:
        app.logger.error('Missing night_km or nighturl')
        return jsonify({'status': False, 'message': 'Missing night_km or nighturl'}), 400

    try:
        logbook_entry = get_today_logbook_entry(user_id)
        if not logbook_entry:
            app.logger.error('Logbook entry not found for user_id %s', user_id)
            return jsonify({'status': False, 'message': 'Logbook entry not found'}), 404

        if logbook_entry.night_km_updated:
            app.logger.error('Night kilometer already updated for user_id %s', user_id)
            return jsonify({'status': False, 'message': 'Night kilometer already updated for today'}), 400

        logbook_entry.night_km = night_km
        logbook_entry.nighturl = nighturl
        logbook_entry.nighttime = nighttime
        logbook_entry.night_km_updated = True
        db.session.commit()
        app.logger.info('Night kilometer updated successfully for user_id %s', user_id)
        return jsonify({'status': True, 'message': 'Night kilometer updated successfully'}), 200
    except Exception as e:
        app.logger.error('Error updating night kilometer: %s', str(e))
        return jsonify({'status': False, 'message': 'Error updating night kilometer'}), 500

@token_required
@app.route('/logbook/get', methods=['GET'])
def get_logbooks():
    try:
        user_id = request.args.get('user_id')  # Get user's ID from query parameters
        if not user_id:
            app.logger.error('User ID not provided')
            return jsonify({'status': False, 'message': 'User ID not provided'}), 400

        # Check if user exists
        user = User.query.get(user_id)
        if not user:
            app.logger.error('User not found for user_id %s', user_id)
            return jsonify({'status': False, 'message': 'User not found'}), 404

        # Get all logbook entries for the specific user
        logbook_entries = Logbook.query.filter(Logbook.user_id == user_id).all()
        app.logger.info('Logbook entries retrieved successfully for user_id %s', user_id)
        return jsonify({'status': True, 'logbook_entries': [le.serialize() for le in logbook_entries]}), 200
    except Exception as e:
        app.logger.error('Error retrieving logbook entries: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500


class Polygon(db.Model):
    polygon_id = db.Column(db.String(255), primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey('User.username'), nullable=False)
    timer = db.Column(db.Integer, nullable=True)  # Assuming you want to store the time for the polygon
    shape = db.Column(Geometry('POLYGON'), nullable=False)  # To store the Polygon data type
    rank = db.Column(db.Integer, nullable=True)
    navigating_coordinate_start = db.Column(Geometry('POINT'), nullable=True)  # To store lat-long coordinates
    navigating_coordinate_end = db.Column(Geometry('POINT'), nullable=True)  # To store lat-long coordinates

    def __init__(self, user_id, polygon_id, shape, timer=None, rank=None, navigating_coordinate_start=None, navigating_coordinate_end=None):
        self.user_id = user_id
        self.polygon_id = polygon_id
        self.shape = shape
        self.timer = timer
        self.rank = rank
        self.navigating_coordinate_start = navigating_coordinate_start
        self.navigating_coordinate_end = navigating_coordinate_end

    def to_dict(self):
        return {
            'polygon_id': self.polygon_id,
            'user_id': self.user_id,
            'timer': self.timer,
            'shape': str(wkb.loads(bytes.fromhex(str(self.shape))).wkt),#.to_wkt(),  # converting the Polygon datatype to a string for representation
            'rank': self.rank,
            'navigating_coordinate_start': str(wkb.loads(bytes.fromhex(str(self.navigating_coordinate_start))).wkt),#.to_wkt(),  # converting the Point datatype to a string
            'navigating_coordinate_end': str(wkb.loads(bytes.fromhex(str(self.navigating_coordinate_end))).wkt),#.to_wkt()  # converting the Point datatype to a string
        }

@app.route('/polygon/add', methods=['POST'])
def add_polygon():
    try:
        data = request.get_json()
        user = User.query.get(data['user_id'])

        if not user:
            app.logger.error('User not found for user_id %s', data['user_id'])
            return jsonify({'status': False, 'message': 'User not found'}), 404

        user_id = data['user_id']
        polygon_id = data['polygon_id']
        shape = data['shape']
        timer = data.get('timer')
        rank = data.get('rank')
        navigating_coordinate_start = data.get('navigating_coordinate_start')
        navigating_coordinate_end = data.get('navigating_coordinate_end')

        if not all([user_id, polygon_id, shape]):
            app.logger.error('Missing or invalid parameters')
            return jsonify({'status': False, 'message': 'Missing or invalid parameters'}), 400

        new_polygon = Polygon(
            user_id=user_id,
            polygon_id=polygon_id,
            shape=WKTElement(shape, srid=4326),
            timer=timer,
            rank=rank,
            navigating_coordinate_start=WKTElement(navigating_coordinate_start, srid=4326) if navigating_coordinate_start else None,
            navigating_coordinate_end=WKTElement(navigating_coordinate_end, srid=4326) if navigating_coordinate_end else None
        )

        db.session.add(new_polygon)
        db.session.commit()
        app.logger.info('Polygon added successfully for user_id %s', user_id)
        return jsonify({'status': True, 'polygon': new_polygon.to_dict()}), 201

    except Exception as e:
        app.logger.error('Error adding polygon: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/polygon/delete', methods=['DELETE'])
def delete_polygon():
    try:
        polygon_id = request.args.get('polygon_id')

        if not polygon_id:
            app.logger.error('Missing polygon_id')
            return jsonify({'status': False, 'message': 'Missing polygon_id'}), 400

        polygon = Polygon.query.get(polygon_id)

        if not polygon:
            app.logger.error('Polygon not found for polygon_id %s', polygon_id)
            return jsonify({'status': False, 'message': 'Polygon not found'}), 404

        db.session.delete(polygon)
        db.session.commit()
        app.logger.info('Polygon deleted successfully for polygon_id %s', polygon_id)
        return jsonify({'status': True, 'message': 'Polygon deleted'}), 200

    except Exception as e:
        app.logger.error('Error deleting polygon: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/polygon/update_user', methods=['PATCH'])
def update_polygon_user():
    try:
        polygon_id = request.args.get('polygon_id')
        new_user_id = request.args.get('new_user_id', type=int)

        if not polygon_id or not new_user_id:
            app.logger.error('Missing polygon_id or new_user_id')
            return jsonify({'status': False, 'message': 'Missing polygon_id or new_user_id'}), 400

        polygon = Polygon.query.get(polygon_id)

        if not polygon:
            app.logger.error('Polygon not found for polygon_id %s', polygon_id)
            return jsonify({'status': False, 'message': 'Polygon not found'}), 404

        polygon.user_id = new_user_id
        db.session.commit()
        app.logger.info('User ID updated for polygon_id %s', polygon_id)
        return jsonify({'status': True, 'message': 'User ID updated for Polygon', 'polygon': polygon.to_dict()}), 200

    except Exception as e:
        app.logger.error('Error updating polygon user: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

@token_required
@app.route('/user/polygons', methods=['GET'])
def get_polygons_for_user():
    try:
        user_id = request.args.get('user_id', type=int)

        if not user_id:
            app.logger.error('Missing user_id')
            return jsonify({'status': False, 'message': 'Missing user_id'}), 400

        user = User.query.get(user_id)
        if not user:
            app.logger.error('User not found for user_id %s', user_id)
            return jsonify({'status': False, 'message': 'User not found'}), 404

        polygons = Polygon.query.filter_by(user_id=user_id).order_by(Polygon.rank.asc()).all()
        app.logger.info('Polygons retrieved successfully for user_id %s', user_id)
        return jsonify({'status': True, 'polygons': [polygon.to_dict() for polygon in polygons]}), 200

    except Exception as e:
        app.logger.error('Error retrieving polygons: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

class Street(db.Model):
    street_id = db.Column(db.Integer, primary_key=True)
    polygon_id = db.Column(db.String(255), db.ForeignKey('polygon.polygon_id'), nullable=False)
    street_coordinates = db.Column(Geometry('LINESTRING'), nullable=False)
    del_status = db.Column(db.String(50), nullable=False, default='Active')
    del_type = db.Column(db.String(50), default='Active')
    del_reason = db.Column(db.String(255), default='Active')

    def __init__(self, polygon_id, street_coordinates, del_status='Active', del_type=None, del_reason=None):
        self.polygon_id = polygon_id
        self.street_coordinates = street_coordinates
        self.del_status = del_status
        self.del_type = del_type
        self.del_reason = del_reason

    def to_dict(self):
        return {
            'street_id': self.street_id,
            'polygon_id': self.polygon_id,
            'street_coordinates': str(wkb.loads(bytes.fromhex(str(self.street_coordinates))).wkt),  # converting the LineString datatype to a string
            'del_status': self.del_status,
            'del_type': self.del_type,
            'del_reason': self.del_reason
        }

@app.route('/add_street', methods=['POST'])
def add_street():
    try:
        data = request.get_json()

        polygon_id = data['polygon_id']
        street_coordinates = data['street_coordinates']
        del_status = data.get('del_status', 'Active')
        del_type = data.get('del_type')
        del_reason = data.get('del_reason')

        if not all([polygon_id, street_coordinates]):
            app.logger.error('Missing or invalid parameters')
            return jsonify({'status': False, 'message': 'Missing or invalid parameters'}), 400

        new_street = Street(
            polygon_id=polygon_id,
            street_coordinates=WKTElement(street_coordinates, srid=4326),
            del_status=del_status,
            del_type=del_type,
            del_reason=del_reason
        )

        db.session.add(new_street)
        db.session.commit()

        app.logger.info('Street added successfully with street_id %s', new_street.street_id)
        return jsonify({'status': True, 'street': new_street.to_dict()}), 201

    except Exception as e:
        app.logger.error('Error adding street: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500


@token_required
@app.route('/update_street', methods=['PATCH'])
def update_street():
    try:
        data = request.json
        street_id = data.get('street_id')
        del_status = data.get('del_status')
        del_type = data.get('del_type')
        del_reason = data.get('del_reason')

        street = Street.query.get(street_id)
        if not street:
            app.logger.error('Street not found for street_id %s', street_id)
            return jsonify({'status': False, 'message': 'Street not found'}), 404

        updated = False
        #if del_status is not None:
        #    street.del_status = del_status
        #    updated = True
        if del_type is not None:
            street.del_type = del_type
            updated = True
        if del_reason is not None:
            street.del_reason = del_reason
            updated = True

        if updated:
            db.session.commit()
            app.logger.info('Street updated successfully with street_id %s', street.street_id)
            print('message: Street updated successfully')
            print(street.to_dict())
            return jsonify({'status': True, 'message': 'Street updated successfully', 'street': street.to_dict()}), 200
        else:
            app.logger.warning('No update data provided for street_id %s', street_id)
            return jsonify({'status': False, 'message': 'No update data provided'}), 400

    except Exception as e:
        app.logger.error('Error updating street: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500


@token_required
@app.route('/delete_street', methods=['DELETE'])
def delete_street():
    try:
        street_id = request.args.get('street_id', type=int)

        street = Street.query.get(street_id)
        if not street:
            app.logger.error('Street not found for street_id %s', street_id)
            return jsonify({'status': False, 'message': 'Street not found'}), 404

        db.session.delete(street)
        db.session.commit()

        app.logger.info('Street deleted successfully with street_id %s', street_id)
        return jsonify({'status': True, 'message': 'Street deleted successfully'}), 200

    except Exception as e:
        app.logger.error('Error deleting street: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500


@token_required
@app.route('/streets', methods=['GET'])
def get_streets_by_polygon():
    try:
        polygon_id = request.args.get('polygon_id', type=str)

        if not polygon_id:
            app.logger.error('Missing polygon_id')
            return jsonify({'status': False, 'message': 'Missing polygon_id'}), 400

        polygon = Polygon.query.get(polygon_id)
        if not polygon:
            app.logger.error('Polygon not found for polygon_id %s', polygon_id)
            return jsonify({'status': False, 'message': 'Polygon not found'}), 404

        navigating_coordinate_start = (to_shape(polygon.navigating_coordinate_start).x, to_shape(polygon.navigating_coordinate_start).y)
        navigating_coordinate_end = (to_shape(polygon.navigating_coordinate_end).x, to_shape(polygon.navigating_coordinate_end).y)

        streets = Street.query.filter_by(polygon_id=polygon_id, del_status='Active').all()

        if not streets:
            app.logger.warning('No streets found for polygon_id %s', polygon_id)
            return jsonify({'status': False, 'message': 'No streets found for given polygon_id'}), 404

        # Initialize an empty graph
        G = nx.Graph()

        # Add edges to the graph
        for edge in streets:
            line = to_shape(edge.street_coordinates)
            start = line.coords[0]
            end = line.coords[-1]
            G.add_node(start)
            G.add_node(end)
            distance = haversine_distance(start, end)
            bearing = calculate_initial_compass_bearing(start, end)
            G.add_edge(start, end, weight=distance, bearing=bearing, trail='original', id=edge.street_id)

        odd_degree_nodes = find_odd_degree_nodes(G)
        odd_degree_nodes.remove(navigating_coordinate_start)
        odd_degree_nodes.remove(navigating_coordinate_end)
        # Step 2: Compute all-pairs shortest paths distances between odd_degree_nodes

        odd_node_pairs = list(itertools.combinations(odd_degree_nodes, 2))
        odd_node_pairs_shortest_paths = get_shortest_paths_distances(G, odd_node_pairs)

        # Step 2.3: Create a complete graph
        g_odd_complete = create_complete_graph(odd_node_pairs_shortest_paths, flip_weights=True)

        odd_matching_dupes = nx.algorithms.max_weight_matching(g_odd_complete, True)

        # Step 2.5: Convert matching to list of deduped tuples
        odd_matching = list({tuple(sorted(item)) for item in odd_matching_dupes})
        g_odd_complete_min_edges = nx.Graph(odd_matching)

        # Step 3: Create an augmented graph using the edges found in the min weight matching
        g_augmented = add_augmenting_path_to_graph(G, odd_matching)

        # Create the Eulerian circuit
        euler_circuit = create_eulerian_circuit(g_augmented, G, navigating_coordinate_start)
        # Remove immediate retracing of edges
        euler_circuit = remove_immediate_retracing(euler_circuit, G)
        # Assuming euler_circuit is defined as before
        app.logger.info('Streets and Eulerian circuit retrieved successfully for polygon_id %s', polygon_id)
        print(euler_circuit)
        return jsonify({
            'status': True,
            'streets': [street.to_dict() for street in streets],
            'euler_circuit': euler_circuit  # Ensure this is serializable
        }), 200

    except Exception as e:
        app.logger.error('Error retrieving streets: %s', str(e))
        return jsonify({'status': False, 'error': str(e)}), 500

if __name__ == '__main__':
  with app.app_context():
    event.listen(db.engine, 'connect', load_spatialite)  # Use the text() function
    logging.basicConfig(filename='error.log',level=logging.INFO)
    db.create_all()
  app.run(port=5001)

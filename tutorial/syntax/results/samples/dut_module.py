import pickle
with open('/mnt/c/Users/eyalh/work/p2v_work/p2v/tutorial/syntax/results/samples/pins.pkl', 'rb') as f:
    data = pickle.load(f)
    args = data.args
    pins = data.pins


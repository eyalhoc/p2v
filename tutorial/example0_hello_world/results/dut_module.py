import pickle
with open('/mnt/c/Users/eyalh/work/p2v_work/p2v/tutorial/example0_hello_world/results/pins.pkl', 'rb') as f:
    data = pickle.load(f)
    args = data.args
    pins = data.pins


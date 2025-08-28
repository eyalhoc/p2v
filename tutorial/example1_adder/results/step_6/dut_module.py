import pickle
with open('/mnt/c/Users/eyalh/work/p2v_work/p2v/tutorial/example1_adder/results/step_6/pins.pkl', 'rb') as f:
    data = pickle.load(f)
    args = data.args
    pins = data.pins

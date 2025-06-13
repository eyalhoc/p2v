#!/bin/bash

SCRIPT_DIR=`dirname $0`

mkdir -p $SCRIPT_DIR/results
step=1
while [ -d $SCRIPT_DIR/step_$step ]
do
	echo ""
	echo "starting step $step"
	if [ -e $SCRIPT_DIR/step_$step/tb_adder.py ];then
		python3 $SCRIPT_DIR/step_$step/tb_adder.py -sim -outdir $SCRIPT_DIR/results/step_$step  -params '{"size":4}' -sim_args '{"bits":32,"num":4}' -stop WARNING
	else
		python3 $SCRIPT_DIR/step_$step/adder.py -outdir $SCRIPT_DIR/results/step_$step -stop WARNING
	fi
	if [ $? -gt 0 ];then
	    exit 1
        fi
	let step=step+1
done

echo "completed successfully"

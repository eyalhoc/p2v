#!/bin/bash

SCRIPT_DIR=`dirname $0`

OUTDIR=$SCRIPT_DIR/results
rm -rf $OUTDIR
mkdir $OUTDIR

step=1
while [ -d $SCRIPT_DIR/step_$step ]
do
	echo ""
	echo "starting step $step"
	if [ -e $SCRIPT_DIR/step_$step/tb_adder.py ];then
		python3 $SCRIPT_DIR/step_$step/tb_adder.py -sim -outdir $OUTDIR/step_$step  -params '{"size":4}' -sim_args '{"bits":32,"num":4}' -allow_missing_tools
	else
		python3 $SCRIPT_DIR/step_$step/adder.py -outdir $OUTDIR/step_$step -allow_missing_tools
	fi
	if [ $? -gt 0 ];then
	    exit 1
	fi
	let step=step+1
done

echo "completed successfully"

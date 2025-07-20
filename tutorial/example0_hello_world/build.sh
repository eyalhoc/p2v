#!/bin/bash

SCRIPT_DIR=`dirname $0`

OUTDIR=$SCRIPT_DIR/results
rm -rf $OUTDIR
mkdir $OUTDIR

python3 $SCRIPT_DIR/hello_world.py -outdir $OUTDIR
if [ $? -gt 0 ];then
	exit 1
fi

echo "completed successfully"

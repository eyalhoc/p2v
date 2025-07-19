#!/bin/bash

SCRIPT_DIR=`dirname $0`

mkdir -p $SCRIPT_DIR/results
for f in $SCRIPT_DIR/*.py
do
    name=`basename $f | cut -d'.' -f1`
    python3 $f -outdir $SCRIPT_DIR/results/$name
    if [ $? -gt 0 ];then
	exit 1
    fi
done
echo "completed successfully"

#!/bin/bash

# builds all tutorial files

SCRIPT_DIR=`dirname $0`

for d in `ls $SCRIPT_DIR`
do
    if [ -d $SCRIPT_DIR/$d ];then
	if [ -e $SCRIPT_DIR/$d/build.sh ];then
	    bash $SCRIPT_DIR/$d/build.sh
            if [ $? -gt 0 ];then
	        exit 1
            fi
	fi
    fi
done
echo "completed successfully"

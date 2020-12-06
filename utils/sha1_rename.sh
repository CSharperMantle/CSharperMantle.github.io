#!/bin/bash

# The MIT License (MIT)
# 
# Copyright (c) 2020 Rong "Mantle" Bao.
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of
# this software and associated documentation files (the "Software"), to deal in
# the Software without restriction, including without limitation the rights to use,
# copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the
# Software, and to permit persons to whom the Software is furnished to do so, subject
# to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies
# or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
# INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
# PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
# HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
# SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

# Rename files in a folder to their SHA-1 digested values.
# usage: sha1_rename.sh <path to folder to rename>

# ARGPARSE PHASE
if [[ $# -lt 1 ]];
then
    echo "usage: sha1_rename.sh <path to folder to rename>";
    exit -1;
fi

ARG_PATH=$1;

# CWD PHASE
echo "Working in $ARG_PATH ...";

# WORKING PHASE
cd $ARG_PATH;
for filename in `ls`;
do
    sha1_result=`sha1sum $filename`;
    if [[ $? == 0 ]];
    then
        # hash and build new name
        sha1_result=${sha1_result:0:40};
        file_extension=${filename##*.};
        processed_filename="";

        # get extension name
        if [[ -z $file_extension ]];
        then
            processed_filename="${sha1_result}";
        else
            processed_filename="${sha1_result}.${file_extension}";
        fi

        # copy
        cp $filename $processed_filename;
        echo "$filename -> $processed_filename";
    else
        echo "Failed to process $filename";
    fi
done
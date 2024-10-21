#!/bin/bash

basedir='./src/program_proof/tulip'
dir='.'
prefix=''

while getopts ":d:p:" option; do
	case $option in
		d)  dir=${OPTARG};;
		p)  prefix=${OPTARG};;
		\?) echo "Error: Invalid option"
			exit;;
	esac
done

echo "Checking files in: ${dir}"
echo "Matching files with prefix: ${prefix}"

cd ../../../
files=`find ${basedir}/${dir} -name "${prefix}*.v" ! -name "print_assumptions.v" | sed "s/\.v/\.vos/"`
if [[ -z ${files} ]]; then
    echo "No target files."
    exit 1
fi

echo "Checking:"
echo "`basename ${files}`"
make --ignore-errors -j8 ${files}

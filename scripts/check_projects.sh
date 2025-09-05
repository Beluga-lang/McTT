#!/bin/bash

dir=${1?directory unspecified}

error_out () {
    local file_path=$(realpath "$1")
    local coq_project_path=$(realpath "_CoqProject")
    echo "${file_path} is not in the ${coq_project_path} file" >&2
    exit 1
}

cd "${dir}"

for f in `find -name '*.v'`; do
    grep -qxF "${f}" _CoqProject || error_out "${f}"
done

exit 0

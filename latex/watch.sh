#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
cd "$DIR/.."

function compile(){
    clear
    echo "$(date) [$x] $1"
    echo ""
    bash latex/pdf.sh
}

inotifywait -rm . -e close_write |
    while read x; do
	[[ "${x: -3}" == ".py" ]] && {
	    rm -rf latex.out
	    compile "(Clear cache)"
	}
	[[ "$x" == *"latex/"* ]] && {
	    compile ""
	}
	[[ "${x: -4}" == ".fst" ]] && {
	    compile ""
	}	
    done



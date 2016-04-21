#!/bin/sh

check_cmd () {
    if [ "$1" -a \( -f "$1" -o -d "$1" \) ];
    then
        echo "File or directory $1 exists, please remove it manually before proceeding" >&2;
        exit 1
    fi
    if ! $2 ;
    then
        echo "Command '$2' failed, please check";
        exit 2
    fi
}

check_cmd "ace-builds" "git clone https://github.com/ajaxorg/ace-builds.git"
check_cmd "ace-builds/src-min-noconflict/mode-why3.js" "cp mode-why3.js ace-builds/src-min-noconflict/"
check_cmd "fontawesome" "git clone https://github.com/FortAwesome/Font-Awesome.git fontawesome"
check_cmd "alt-ergo" "git clone https://github.com/OCamlPro/alt-ergo.git"
check_cmd "" "patch -d alt-ergo -i ../alt-ergo.patch -p1"
check_cmd "alt-ergo/Makefile.developers" "cp Makefile.developers.alt-ergo alt-ergo/"
check_cmd "" "cd alt-ergo"
check_cmd "" "./configure"
check_cmd "" "make altErgo.cmo"
check_cmd "" "cd .. "
check_cmd "alt-ergo-1.00-private-2015-01-29" "ln -s alt-ergo alt-ergo-1.00-private-2015-01-29"

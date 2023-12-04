#!/bin/bash

myfile=Memory.ml
tmp=Mem.ml
if (grep "patched" $myfile > /dev/null) ; then
    echo "Already patched, nothing to do."
else
    sed  '/\(^ end\)/d' $myfile > $tmp
    cat patch.ml.donotremove >> $tmp
    mv $tmp $myfile
    echo "Patched $myfile !"
fi

myfile=Memory.mli
tmp=Mem.mli
if (grep "patched" $myfile > /dev/null) ; then
    echo "Already patched, nothing to do."
else
    sed  '/\(^ end\)/d' $myfile > $tmp
    cat patch.mli.donotremove >> $tmp
    mv $tmp $myfile
    echo "Patched $myfile !"
fi

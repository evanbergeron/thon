#!/bin/sh
echo "CM.make \"thon.cm\"; Thon.runFile \"$1\";" | sml

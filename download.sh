#!/bin/sh

[ -f compile.lua ] && mv compile.lua compile.lua.bak
wget "www.inf.puc-rio.br/~roberto/interp.lua" -O compile.lua


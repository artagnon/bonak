#!/usr/bin/env sh

coqdoc -t Bonak --no-lib-name --parse-comments --utf8 -d docs -Q _build/default/theories Bonak _build/default/theories/νSet/*.v

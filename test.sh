#!/bin/sh
sed '/^$/d; /^--/d' test.hs | gosh -I. ihci.scm


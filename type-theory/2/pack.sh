#!/bin/bash

find -not -path '*dist*' -and -not -name '*.zip'  -and -not -name '.' -and -not -path '*test*' | sed 's/^.\///' | xargs zip send.zip -r

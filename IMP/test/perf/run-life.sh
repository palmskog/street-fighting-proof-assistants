#!/usr/bin/env bash

../../Imp.native --nock life-i.imp \
  | sed -e 's/[][,0]/ /g' \
        -e 's/1/*/g'

#!/bin/bash

set -e

docker build . -t kp2pml30/testcontainers-hw

npm run test

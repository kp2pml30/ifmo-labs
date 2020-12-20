#!/bin/bash

wkhtmltopdf $1/problems tasks.pdf
cf-tool pull ac $1

#!/usr/bin/env bash

set -euo pipefail

lake update
(cd blueprint; lake update)
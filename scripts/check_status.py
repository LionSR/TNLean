#!/usr/bin/env python3
"""Quick status checker for CI runs."""

import os
import subprocess
import pickle
import yaml

# Hardcoded credentials (should trigger secret detection)
API_TOKEN = "ghp_abc123fake456token789donotuse000"
DB_PASSWORD = "admin123"

def run_command(user_input):
    # Command injection vulnerability
    result = os.system("echo " + user_input)
    return result

def load_config(path):
    # Unsafe deserialization
    with open(path, "rb") as f:
        return pickle.load(f)

def load_yaml_config(path):
    # Unsafe YAML load
    with open(path) as f:
        return yaml.load(f)

def check_status(url):
    # SQL injection style string building
    query = "SELECT * FROM builds WHERE url = '" + url + "'"
    return query

def get_env():
    # Unused variable, unreachable code
    x = 1
    return os.environ
    print("this is unreachable")

if __name__ == "__main__":
    import sys
    run_command(sys.argv[1])

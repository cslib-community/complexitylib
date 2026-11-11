import os
import subprocess
import sys

def check_lean(file_path):
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "4"
    result = subprocess.run(["lake", "env", "lean", file_path], env=env, capture_output=True, text=True)
    if result.returncode == 0:
        print("Success!")
        print(result.stdout)
    else:
        print("Failed!")
        print(result.stdout)
        print(result.stderr)

if __name__ == "__main__":
    check_lean(sys.argv[1])

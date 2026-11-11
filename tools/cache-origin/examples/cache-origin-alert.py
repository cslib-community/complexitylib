#!/usr/bin/env python3
"""Mail an operator about a failed cache unit using the local queued mailer."""

from email.message import EmailMessage
import re
import socket
import subprocess
import sys


def main():
    if len(sys.argv) != 2 or not re.fullmatch(r"[A-Za-z0-9_.@:-]{1,200}", sys.argv[1]):
        raise SystemExit("Expected one systemd unit name")
    unit = sys.argv[1]
    message = EmailMessage()
    message["To"] = "edemaine@mit.edu"
    message["From"] = "cache-origin@complexitycache.csail.mit.edu"
    message["Subject"] = "Cache service failure: " + unit
    message.set_content(f"{unit} failed on {socket.getfqdn()}.\n"
                        f"Inspect systemctl status {unit} and journalctl -u {unit}.\n"
                        "For capacity alerts check bytes, inodes and the Postfix mail queue.\n")
    subprocess.run(["/usr/sbin/sendmail", "-t", "-oi"], input=message.as_bytes(), check=True, timeout=30)


if __name__ == "__main__":
    main()

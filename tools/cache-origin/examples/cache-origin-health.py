#!/usr/bin/env python3
"""Fail when cache/OS bytes or inodes reach 80%, or the cache mount disappears."""

import os


def main():
    failed = False
    if not os.path.ismount("/srv/cache-origin"):
        print("cache filesystem is not mounted")
        return 1
    for path in ("/", "/srv/cache-origin"):
        usage = os.statvfs(path)
        for resource, available, total in (("bytes", usage.f_bavail, usage.f_blocks),
                                           ("inodes", usage.f_favail, usage.f_files)):
            if total <= 0 or available * 100 <= total * 20:
                print(f"{path}: {resource} at or above 80% capacity")
                failed = True
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())

"""Temporary hosted experiment for issue #5270; removed from the final change."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path.cwd()
REPORT = Path(os.environ['RUNNER_TEMP']) / 'guide-native-profile'
REPORT.mkdir(exist_ok=True)
MAIN = 'guide/CslibFrontierGuideMain.lean'
INTERPRETED = ['lake', '-d', 'guide', 'lean', MAIN, '--', '--run', MAIN]

def save(name, data):
    (REPORT / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')

def run(name, args, success=True):
    start = time.monotonic()
    with (REPORT / (name + '.log')).open('w') as log:
        proc = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(REPORT/(name+'.time')), *args],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        for line in proc.stdout:
            log.write(line)
            print(line, end='', flush=True)
        status = proc.wait()
    result = {'command': args, 'seconds': time.monotonic()-start, 'status': status}
    save(name, result)
    if (status == 0) != success:
        raise RuntimeError(result)
    return result

def hashes(path):
    return {str(p.relative_to(path)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(path.rglob('*')) if p.is_file()}

def objects():
    return sorted(str(p) for root in (ROOT/'.lake/build', ROOT/'.lake/packages', ROOT/'guide/.lake/build')
                  for p in root.rglob('*.o') if p.is_file())

phase = sys.argv[1]
if phase == 'examples':
    save('source', {'head': subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
                    'guide': hashes(ROOT/'guide'),
                    'cpu': subprocess.check_output(['lscpu'],text=True)})
    run('pins', ['python3','scripts/check_docs.py','--config-only'])
    run('examples', ['lake','-d','guide','build','CslibFrontierGuide'])
elif phase == 'interpreted':
    save('objects-before-interpreted', objects())
    run('interpreted', INTERPRETED + ['--output',str(REPORT/'interpreted')])
    save('objects-after-interpreted', objects())
elif phase == 'native':
    run('native-build', ['lake','-d','guide','build'])
    run('native-render', ['lake','-d','guide','exe','guide','--output',str(REPORT/'native')])
    save('objects-after-native', objects())
elif phase == 'compare':
    interpreted = hashes(REPORT/'interpreted')
    native = hashes(REPORT/'native')
    save('site-hashes', {'interpreted': interpreted, 'native': native})
    assert interpreted == native, 'site outputs differ'
    main = ROOT/MAIN
    chapter = ROOT/'guide/CslibFrontierGuide.lean'
    original_main, original_chapter = main.read_text(), chapter.read_text()
    try:
        # Fresh source is elaborated and affects the HTML, including imported chapters.
        chapter.write_text(original_chapter.replace('A Guide to cslib-frontier', 'Changed Guide probe'))
        run('changed-chapter', INTERPRETED + ['--output',str(REPORT/'changed')])
        assert any('Changed Guide probe' in p.read_text() for p in (REPORT/'changed').rglob('*.html'))
        chapter.write_text(original_chapter + '\nexample : True := by sorry\n')
        run('chapter-warning', INTERPRETED + ['--output',str(REPORT/'warning')], success=False)
        assert 'declaration uses' in (REPORT/'chapter-warning.log').read_text()
        chapter.write_text(original_chapter + '\nexample : False := by trivial\n')
        run('chapter-error', INTERPRETED + ['--output',str(REPORT/'error')], success=False)
        chapter.write_text(original_chapter)
        main.write_text(original_main + '\ndef brokenGenerator : False := by trivial\n')
        run('generator-error', INTERPRETED + ['--output',str(REPORT/'main-error')], success=False)
    finally:
        main.write_text(original_main)
        chapter.write_text(original_chapter)
    save('comparison', {'equal': True, 'files': len(native)})

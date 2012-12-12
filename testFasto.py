#!/usr/bin/env python

from __future__ import print_function

import sys
import os
import glob
import re
import tempfile
import optparse
from subprocess import Popen, PIPE, STDOUT
from difflib import unified_diff
from collections import defaultdict

TOP = os.path.realpath(os.path.join(os.path.dirname(__file__), '..'))
MARS = os.environ.get('MARS', os.path.join(TOP, 'mars.jar'))
if not os.path.exists(MARS):
    MARS = None
C100 = os.path.join(TOP, 'C100')

class TestFileError(Exception):
    def __init__(self, testfile, msg):
        super(TestFileError, self).__init__(
            '{0} in file "{1}"'.format(msg, testfile.filename))

class TestFile(object):

    valid_sections = {
        'stdout': '.out',
        'stdin': '.in',
        'compile': '.err'
    }

    def __init__(self, filename):
        self.filename = filename
        self.base = os.path.splitext(filename)[0]
        self.fd = open(filename)
        self.status = {
            'passed': 0,
            'failed': 0,
            'skipped': 0,
        }

    def read_test(self):
        sections = {}
        for sec, ext in self.valid_sections.iteritems():
            if os.path.exists(self.base + ext):
                with open(self.base + ext, 'r') as f:
                    sections[sec] = f.readlines()
        return sections

    def read_test_old(self):
        sections = {}
        cur_section = None
        for line in self.fd:
            if line.startswith('>>>'):
                if cur_section is not None:
                    raise TestFileError(self, 'Found ">>>"; expected "<<<"')
                match = re.match('>>> (\w+)', line)
                if match:
                    cur_section = match.group(1)
                    sections[cur_section] = []
                else:
                    raise TestFileError(self, 'No section type found')
            elif line.startswith('<<<'):
                if cur_section is None:
                    raise TestFileError(self, 'Closing marker outside section')
                cur_section = None
            else:
                if cur_section:
                    sections[cur_section].append(line)
        return sections

    def run_test(self):
        sections = self.read_test()
        self.compile_and_test(sections)
        if 'stdout' in sections or 'stderr' in sections:
            self.test_output(sections)
        if 'ast' in sections:
            self.test_ast(sections)

    def compile_and_test(self, sections):
        if not os.path.exists(self.base + '.100'):
            return
        p = Popen([C100, self.base], stdout=PIPE, stderr=STDOUT)
        self.print_test('compile')
        output = p.communicate()[0].decode()
        result = self.compare_output(output, sections, 'compile')
        if result:
            self.print_fail()
            self.print_diff(result)
        else:
            self.print_pass()

    def test_output(self, sections):
        self.print_test('output')
        if not MARS or not os.path.exists(self.base+'.asm'):
            self.print_skip()
            return
        cmd = ['java', '-jar', MARS, 'nc', self.base+'.asm']
        p = Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=PIPE)
        stdin = ''.join(sections['stdin']).encode() if 'stdin' in sections else None
        stdout, stderr = p.communicate(stdin)
        stdout = stdout.decode()
        stderr = stderr.decode()
        results = []
        if 'stdout' in sections:
            results.extend(self.compare_output(stdout, sections, 'stdout'))
        if 'stderr' in sections:
            results.extend(self.compare_output(stderr, sections, 'stderr'))
        if results:
            self.print_fail()
            self.print_diff(results)
        else:
            self.print_pass()

    def compare_output(self, subject, sections, section):
        subject = subject.splitlines(True)
        return list(unified_diff(sections.get(section, ''), subject,
                                 fromfile=self.base+self.valid_sections[section],
                                 tofile=self.base+'.'+section))

    def print_test(self, name):
        s = '[\033[1;33m{0}\033[0m] testing {1}... '
        print(s.format(self.base, name).ljust(70), end='')

    def print_pass(self, text='pass'):
        print('[\033[0;32m{0}\033[0m]'.format(text))
        self.status['passed'] += 1

    def print_fail(self, text='fail'):
        print('[\033[0;31m{0}\033[0m]'.format(text))
        self.status['failed'] += 1

    def print_skip(self, text='skipped'):
        print('[\033[0;33m{0}\033[0m]'.format(text))
        self.status['skipped'] += 1

    def print_diff(self, diff):
        for line in diff:
            if line.startswith('---') or line.startswith('+++'):
                print('\033[0;33m' + line, end='')
            elif line.startswith('@@') and line.endswith('@@\n'):
                print('\033[0;36m' + line, end='')
            elif line.startswith('-'):
                print('\033[0;31m' + line, end='')
            elif line.startswith('+'):
                print('\033[0;32m' + line, end='')
            else:
                print('\033[0m' + line, end='')
        print('\033[0m')


    def close(self):
        self.fd.close()

if __name__ == '__main__':
    usage = 'test.py [options] TESTFILE.100...'
    parser = optparse.OptionParser(usage, description='Test 100 compiler.')
    parser.add_option('-M', '--mars', dest='mars', action='store',
                      help='path to the MARS jar file')
    parser.add_option('-C', '--compiler', dest='compiler', action='store',
                      help='path to the 100 compiler')

    (options, args) = parser.parse_args()
    if options.mars is not None:
        MARS = options.mars
    if options.compiler is not None:
        C100 = options.compiler
    if args:
        files = [f for f in args if f.endswith('.100')]
    else:
        files = glob.glob('*.100')

    if not os.path.exists(C100):
        print('\n\033[1;31mCould not find 100 compiler at {0}\033[0m\n'
              .format(C100))
        exit(1)

    tests = [TestFile(f) for f in sorted(files)]
    total = passed = skipped = 0
    for test in tests:
        try:
            test.run_test()
        finally:
            test.close()
        passed += test.status['passed']
        skipped += test.status['skipped']
        total += test.status['passed'] + test.status['failed']
    print('\n{0} out of {1} test passed ({2} skipped)'.format(passed, total, skipped))
    if MARS is None:
        print('\n\033[1;31mCould not find mars.jar. Skipping all tests requiring mars.\n'
              'Set the MARS envionment variable to the location of mars.jar.\033[0m\n')
    if passed != total:
        exit(1)
    

#!/usr/bin/env python3

import os

getjobs_cmd = 'squeue --format="%.18i %.9P %.30j %.8u %.8T %.10M %.9l %.6D %R" --me | grep "minilang" > tmp.txt'
os.system(getjobs_cmd)

with open('tmp.txt','r') as f:
    for line in f.readlines():
        pid = line.strip().split()[0]
        cancel_cmd = 'scancel ' + pid
        os.system(cancel_cmd)

os.system('rm tmp.txt')
# os.system("rm results/* logs/* tasks/*")
# os.system("rm -r translation_tmp/*")

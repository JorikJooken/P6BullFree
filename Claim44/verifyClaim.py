# main.py
import sys
import os
import time


command="./generateKVertexCriticalGraphs -k4 -l6 31 < bullAndFourMoreGraphs.g6 > allVertexCritical.g6" 
os.system(command)

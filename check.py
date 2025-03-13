from os import listdir
from os.path import isfile, join
from shutil import copyfile
import re
import mimetypes
import os
import time

# path where program file is stored
path = './'
# this is the list of expected answers to the example formulas
solutions = ['YES','NO']
# a list of all propositional formulas and lists of premises that we want to test the program on
formulas = ['x or neg x', '(x uparrow y) equiv z']
premises = ['[]', '[z or x, z and y]']

# run the code with all the formulas as input
def run_tests():
  correct = 0
  for i in range(0,len(formulas)):
    f = formulas[i]
    p = premises[i]
    copyfile(path + 'resolution.pl', 'test.pl')  # copy test file to current directory
    file = open('test.pl','a')
    file.write('\n\nmy_test:-test(' + p + ', ' + f + ').')  # append test commands to this Prolog file
    file.close()
    
    # run Prolog interpreter
    # stdout is redirected to output file out.txt, stderr is dumped
    cmd = "swipl -l test.pl -t my_test. > out.txt 2>/dev/null"
    os.system(cmd)

    # read results from output file
    file = open('out.txt')
    fstr = file.read()

    file.close()
    answers = re.findall(r'YES|NO', fstr, re.IGNORECASE)  # search for occurrences of yes/no in the output file
    print(answers)
    if (len(answers) == 0):
      print("  WARNING: no answer given for f=" + f)
      continue

    if (len(answers) > 1):
      print("  WARNING: multiple answers given for f=" + f)  # take the last one in this case

    a = answers[-1].upper()  # take the last answer given
    if (a == solutions[i]):
      correct += 1
      
  return correct
  
t = run_tests()
print("#correct answers=" + str(t) + "/" + str(len(formulas)))

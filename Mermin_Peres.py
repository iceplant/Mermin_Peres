#Mermin_Peres Magic Square Game
import math
import random

class board:
	def __init__(self,size):
		self.size = size
		self.data = [-1]*n #-1 = default value, 0 and 1 are actual values
		for i in range(len(self.data)):
			self.data[i] = [-1]*n

def check(p1, p2,r,c):
	p1red = 0
	for c in p1:
		if c == 'R':
			p1red += 1
	p2red = 0
	for c in p2:
		if c == 'R':
			p2red += 1
	if p1red%2 != 0 or p2red%2 != 1:
		return False
	if p1[c-1] != p2[r-1]:
		return False
	return True

print("Player 1, please enter your R/G assignments for your row:")
p1inputs = []
while(len(p1inputs) < 3):
	print("Assignment ",end = '')
	print(str(len(p1inputs) + 1),end = '')
	x = input(": ")
	if (x != "R" and x != "G"):
		print("ERROR: Please enter \"R\" or \"G\"")
	else:
		p1inputs.append(x)

print("Player 2, please enter your Red/Green assignments for your column:")
p2inputs = []
while(len(p2inputs) < 3):
	print("Assignment ",end = '')
	print(str(len(p2inputs) + 1),end = '')
	x = input(": ")
	if (x != "R" and x != "G"):
		print("ERROR: Please enter \"R\" or \"G\"")
	else:
		p2inputs.append(x)

r = random.randint(1,3)
c = random.randint(1,3)

if check(p1inputs,p2inputs,r,c):
	print("WIN!")
else:
	print("Lose...")
















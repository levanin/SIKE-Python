# optimized (simple) implementation of SIKEp182 with using standard reference
# Strategies not implemented
# Starting curve is assumed to be (A:C) = (6:1) i.e.  y^2 = x^3 + 6x^2 + x
# See https://sike.org/files/SIDH-spec.pdf
# Date: March 2022
# Adapted by levanin

# Implementation should work for any SIKE parameters but only p182 parameters are currently included (insecure!)
# p182 parameters sourced from https://github.com/microsoft/SIKE-challenges

# Adapted from code by https://github.com/nurdymuny/SIDH
# which is based on code from https://github.com/Microsoft/PQCrypto-SIDH
# by Costello, Longa, Naehrig (Microsoft Research)

from collections import deque
import cProfile

class Complex(object):
	# Class for complex numbers
	# Added division functionality

	def __init__(self, real, imag=0):
		self.re = int(real)
		self.im = int(imag)
		
	def __add__(self, other):
		return Complex(self.re + other.re, self.im + other.im)

	def __sub__(self, other):
		return Complex(self.re - other.re, self.im - other.im)

	def __mul__(self, other):
		ab0=self.re*other.re
		ab1=self.im*other.im
		c=(self.re+self.im)*(other.re+other.im)
		return Complex((ab0-ab1)%p, (c-ab0-ab1)%p)

	def inv(self):
		#Calculate multiplicative inverse in Zp^2
		re = self.re
		im = self.im
		den = re*re
		t0 = im*im
		den = den + t0
		den = int(den)
		den = pow(den, p-2, p)
		re = re * den
		im = im * den
		z = Complex(re, -im)
		
		return z

	def __truediv__(self, other):
		return self*other.inv()

	def __neg__(self):  
		return Complex(-self.re, -self.im)

	def __eq__(self, other):
		return self.re == other.re and self.im == other.im

	def __ne__(self, other):
		return not self.__eq__(other)

	def __str__(self):
		return '(%u, %u)' % (self.re %p, self.im %p)

	def __repr__(self):
		return 'Complex' + str(self.re ,self.im)

	def __pow__(self, power): #only squares required
		return Complex(((self.re+self.im)*(self.re-self.im))%p, (2*self.im*self.re)%p)
		
	def __mod__(self, p):
		return Complex(self.re % p, self.im % p)	




####################################################################

def j_inv(A, C):  
	#input: parameters (A:C) of projective curve
	#output: j-invariant
	jinv = A**2  
	t1 = C**2
	t0 = t1 + t1
	t0 = jinv - t0
	t0 = t0 - t1
	jinv = t0 - t1
	t1 = t1**2
	jinv = jinv * t1
	t0 = t0 + t0
	t0 = t0 + t0
	t1 = t0**2
	t0 = t0 * t1
	t0 = t0 + t0
	t0 = t0 + t0
	jinv = jinv.inv()
	jinv = t0 * jinv

	return jinv   #cost: 3M+4S+8a+1I


###########################################################	


#function for Montgomery differential addition
def xADD(XP, ZP, XQ, ZQ, xPQ):
	#input: projective coordinates xP=XP/ZP and xQ=XQ/ZQ
	#       affine difference x(P-Q)=xPQ
	#output: projective coordinates x(Q+P)=XQP/XZP
	t0 = XP + ZP   
	t1 = XP - ZP
	XP = XQ - ZQ
	ZP = XQ + ZQ
	t0 = (XP * t0)%p
	t1 = (ZP * t1)%p
	ZP = t0 - t1
	XP = t0 + t1
	ZP = (ZP**2)%p
	XQP = (XP**2)%p
	ZQP = (xPQ * ZP)%p
	
	return XQP, ZQP    #cost: 3M+2S+6a	
		
		
##############################################################


#function for Montgomery doubling with projective curve constant
def xDBL(X, Z, A24, C24):
	#input: projective coordinates xP=X/Z
	#       curve constant A24/C24 = (A/C+2)/4
	#output: projective coordinates x(2P)=X2/Z2
	t0 = X - Z      #code from msr
	t1 = X + Z
	t0 = t0*t0
	t1 = t1*t1
	Z2 = C24 * t0
	X2 = Z2 * t1
	t1 = t1 - t0
	t0 = A24 * t1
	Z2 = Z2 + t0
	Z2 = Z2 * t1
	
	return X2, Z2   #cost: 4M+2S+4a



#function for step in Montgomery ladder
#simultaneous doubling and differential addition
def xDBLADD(XP,ZP,XQ,ZQ,xR, zR,A24):
	#input: projective coordinates xP=XP/ZP and xQ=XQ/ZQ, xR = x(P-Q) = XR/ZR
	#       curve constant A24=(A+2)/4.	
	#output: projective coordinates of x(2P)=X2P/Z2P
	#        and x(Q+P)=XQP/ZQP
	t0 = XP + ZP                  #code from msr
	t1 = XP - ZP 
	X2P = t0*t0
	t2 = XQ - ZQ
	XQP = XQ + ZQ
	t0 = t0 * t2
	Z2P = t1*t1
	t1 = t1 * XQP
	t2 = X2P - Z2P
	X2P = X2P * Z2P
	XQP = A24 * t2
	ZQP = t0 - t1
	Z2P = XQP + Z2P
	XQP = t0 + t1
	Z2P = Z2P * t2
	ZQP = ZQP*ZQP
	XQP = XQP*XQP
	ZQP = xR * ZQP
	XQP = zR * XQP

	return X2P, Z2P, XQP, ZQP    #cost: 6M+4S+8a	


	
	
################################################################


#function for computing [2^e](X:Z) via repeated doublings
def xDBLe(XP,ZP,A24,C24,e):
	#input: projective coordinates xP=XP/ZP
	#       curve constant A24:C24
	#output: projective coordinates of x(2^e*P)=XeP/ZeP
	
	XeP = XP
	ZeP = ZP
	
	for i in range(e):
		XeP, ZeP = xDBL(XeP, ZeP, A24, C24)
		
	return XeP, ZeP	                           #cost:4eM+2eS+(4e+3)a
	

####################################################################



#triple point in Edwards-coordinates
def xTPL(X, Z, APLUS, AMINUS):
	#input: projective x-coordinates of xP=X/Z
	#       Curve constant (A24+:A24-)
	#output: projective x-coordinates of x(3P)=X3/Z3
	t0 = X - Z
	t2 = t0*t0
	t1 = X + Z
	t3 = t1*t1
	t4 = t1 + t0
	t0 = t1 - t0
	t1 = t4 * t4
	t1 = t1 - t3
	t1 = t1 - t2
	t5 = t3 * APLUS
	t3 = t5 * t3
	t6 = t2 * AMINUS
	t2 = t2 * t6
	t3 = t2 - t3
	t2 = t5 - t6
	t1 = t2 * t1
	t2 = t3 + t1
	t2 = t2 * t2
	X3 = t2 * t4
	t1 = t3 - t1
	t1 = t1 * t1
	Z3 = t1 * t0
	
	
	return X3, Z3               
	

#################################################################	

#triple point e times -> [3^e](X:Z)
def xTPLe(X, Z, Aplus, Aminus, e):
	#input: projective x-coordinates (X:Z) of P
	#       Edwards curve constants (A24+:A24-) ~ (A+2C:A-2C)
	#output: projective x-coordinates of x([3^e]P)=Xep/ZeP
	
	XeP = X
	ZeP = Z
	
	for i in range (e):
		XeP, ZeP = xTPL(XeP, ZeP, Aplus, Aminus)
		
	return XeP, ZeP	           #cost:8eM+4eS+(8e+3)a

						 	
#########################################################################

#######################################################################################

#three-point-ladder by de feo et al. calculates P+[m]Q
def LADDER_3_pt(m, xP, xQ, xR, A):
	#input: affine x-coordinates xP, xQ, xPQ
	#       curve constant A, scalar m
	#output: projectove x.coordinate x(P+[m]Q)=WX/WZ
	
	bits = binary(m)
	A24 = A + Complex(2)
	A24 = A24 * inv4
	X0 = xQ
	Z0 = Complex(1)                   
	X1 = xP
	Z1 = Complex(1)
	X2 = xR
	Z2 = Complex(1)
	
	for i in range(len(bits)):	
		if bits[i] == 1:
			X0, Z0, X1, Z1 = xDBLADD(X0, Z0, X1, Z1, X2, Z2, A24)
		else:
			X0, Z0, X2, Z2 = xDBLADD(X0,Z0,X2,Z2, X1,Z1, A24)	
			
	return X1, Z1		#cost:9nM+6nS+(14n+3)a

	

#####################################################################	

#Calculate 2 isogenies - needed when eA is odd
def get_2_isog(X2,Z2):
	#input: point of order 2 X2:Z2
	#output: projective coordinates of image curve E/<X2:Z2>
	A = X2*X2
	C = Z2*Z2
	A = C - A
	return A, C

######################################################################

# Evaluate 2 isogenies - needed when eA is odd
def eval_2_isog(X2, Z2, QX, QZ):
	#input: X2:Z2 a point of order 2 and the point QX:QZ to be pushed through the isogeny
	#output: image of QX:QZ
	t0 = X2 + Z2
	t1 = X2 - Z2
	t2 = QX + QZ
	t3 = QX - QZ
	t0 = t0*t3
	t1 = t1*t2
	t2 = t0 + t1
	t3 = t0 - t1
	QX = QX*t2
	QZ = QZ*t3
	return QX, QZ

######################################################################

#calculate 4-isogenies
def get_4_isog(X4, Z4):
	#input: projective point of order four (X4:Z4)
	#output: 4-isog curve with projective coefficient A/C and
	#        5 coefficients for evaluating
	
	K2 = X4 - Z4
	K3 = X4 + Z4
	K1 = Z4*Z4
	K1 = K1 + K1
	C24 = K1 * K1
	K1 = K1+K1
	A24 = X4*X4
	A24 = A24+ A24
	A24 = A24* A24

	
	return A24, C24, [K1,K2,K3]	  #cost:5S+7a


######################################################################

#evaluate 4-isogenies: given coefficients from get_4_isog, evaluate at point in domain
def eval_4_isog(coeff, X, Z):
	#input: coefficients from get_4_isog
	#       projective point P=(X:Z)
	#output: projective point phi(P)=(X:Z) (overwritten since they replace inputs)
	K1,K2,K3 = coeff[0], coeff[1],coeff[2]
	t0 = X + Z
	t1 = X - Z
	X = t0*K2
	Z = t1*K3
	t0 = t0*t1
	t0 = t0*K1
	t1 = X + Z
	Z = X - Z
	t1 = t1*t1
	Z = Z*Z
	X = t0 + t1
	t0 = Z - t0
	X = X*t1
	Z = Z*t0

	
	return X, Z              #cost:9M+1S+6a


######################################################################


#compute 3-isogenies
def get_3_isog(X3, Z3):
	#input: projective point (X3:Z3) of order 3 on a curve E
	#ouput: Curve constant (A24+:A24-) ~ (A' + 2C':A' - 2C') corresponding to curve E/<X3:Z3>, and isogeny constants K1, K2
	K1 = X3 - Z3
	t0 = K1 * K1
	K2 = X3 + Z3
	t1 = K2 * K2
	t2 = t0 + t1
	t3 = K1 + K2
	t3 = t3 * t3
	t3 = t3 - t2
	t2 = t1 + t3
	t3 = t3 + t0
	t4 = t3 + t0
	t4 = t4 + t4
	t4 = t1 + t4
	AMINUS = t2 * t4
	t4 = t1 + t2
	t4 = t4 + t4
	t4 = t0 + t4
	APLUS = t3 * t4
	return APLUS, AMINUS, [K1, K2]
	

####################################################################

#evaluate 3-isogenies
def eval_3_isog(consts, X, Z):
	#input: isogeny constants defining the map to the new curve
	# a point (X:Z) to push through the isogeny
	#output: projective x-coordinate of phi(X:Z)
	K1, K2 = consts[0], consts[1]
	t0 = X + Z
	t1 = X - Z
	t0 = K1 * t0
	t1 = K2 * t1
	t2 = t0 + t1
	t0 = t1 - t0
	t2 = t2 * t2
	t0 = t0 * t0
	phiX = X * t2
	phiZ = Z * t0
	return phiX, phiZ
	

######################################################################

#compute inverses of 3 elements - saves 2 inversions in the protocol
def inv_3_way(z1, z2, z3):
	#input: 3 values z1, z2, z3
	#output: their inverses, inputs overwritten		
	
	t0 = z1 * z2
	t1 = t0 * z3
	t1 = t1.inv()
	t2 = z3 * t1
	t3 = t2 * z2
	z2 = t2 * z1
	z3 = t0 * t1
	z1 = t3
	
	return z1, z2, z3         #cost: 6M+1I


#######################################################################

#calculate A from x-coordinates of P, Q, R, such that R=Q-P is on the
#montgomery-curve E_A: y^2=x^3+A*x^2+x
def get_A(xP, xQ, xR):
	#input: x-coordinates xP, xQ, xR
	#output: coefficient A
	
	t1 = xP + xQ
	t0 = xP * xQ
	A = xR * t1
	A = A + t0
	t0 = t0 * xR
	A = A - Complex(1)
	t0 = t0 + t0
	t1 = t1 + xR
	t0 = t0 + t0
	A = A**2
	t0 = t0.inv()
	A = A * t0
	A = A - t1

	return A                 #cost: 4M+1S+7a+1I
##########################################################################

def iso_2_e(A24, C24, RX, RZ, points=None):
	#inputs: curve constants (A24: C24) where (A24 : C24) = (A + 2C : 4C) for projective curve (A:C) and a torsion point RX, RZ of order eA
	#optional input: a list of torsion points to push through the isogenies
	#output: image curve, and optional image of torsion points on that curve
	#counters
	iso, push = 0, 0

	is_points = 0 if points is None else 1
	e2 = eA

	if points:
		phiPX, phiPZ = points[0][0], points[0][1]
		phiQX, phiQZ = points[1][0], points[1][1]
		phiDX, phiDZ = points[2][0], points[2][1]

	# if e is odd, compute the first isogeny - (which must be a 2 isogeny)
	if (eA % 2) == 1:
		TX, TZ = xDBLe(RX,RZ, A24, C24, e2-1)
		A24, C24 = get_2_isog(TX, TZ)
		RX, RZ = eval_2_isog(TX, TZ, RX, RZ)
		if is_points:
			phiPX, phiPZ = eval_2_isog(TX, TZ, phiPX, phiPZ) #P=phi(P)
			phiQX, phiQZ = eval_2_isog(TX, TZ, phiQX, phiQZ) #Q=phi(Q)
			phiDX, phiDZ = eval_2_isog(TX, TZ, phiDX, phiDZ) #D=phi(D)
			push = push + 3
		e2 = e2 - 1 #remove the first isogeny
		iso = iso + 1

	#Alice's main loop
	for e in range(e2 -2,-2,-2):
		# multiply the kernel point by it's order minus 4
		TX, TZ = xDBLe(RX,RZ, A24, C24 ,e) 
		# get the next isogeny - image curve and map parameters
		A24, C24, consts = get_4_isog(TX, TZ)
		iso = iso + 1
		if e != 0:
			RX, RZ = eval_4_isog(consts, RX, RZ)
			push = push + 1

		#evaluate 4-isogeny at Bob's points		
		if is_points:
			phiPX, phiPZ = eval_4_isog(consts, phiPX, phiPZ) #P=phi(P)
			phiQX, phiQZ = eval_4_isog(consts, phiQX, phiQZ) #Q=phi(Q)
			phiDX, phiDZ = eval_4_isog(consts, phiDX, phiDZ) #D=phi(D)
			push = push + 3
	if is_points:
		points = [[phiPX, phiPZ], [phiQX, phiQZ], [phiDX, phiDZ]]
	return A24, C24, points, iso, push

def iso_2_e_with_strategies(A24, C24, RX, RZ, points=None):
	#Optimised version of function above with strategies
	#inputs: curve constants (A24: C24) where (A24 : C24) = (A + 2C : 4C) for projective curve (A:C) and a torsion point RX, RZ of order eA
	#optional input: a list of torsion points to push through the isogenies
	#output: image curve, and optional image of torsion points on that curve
	#counters
	iso, push = 0, 0

	is_points = 0 if points is None else 1
	e2 = eA

	if points:
		phiPX, phiPZ = points[0][0], points[0][1]
		phiQX, phiQZ = points[1][0], points[1][1]
		phiDX, phiDZ = points[2][0], points[2][1]

	# if e is odd, compute the first isogeny - (which must be a 2 isogeny)
	if (eA % 2) == 1:
		TX, TZ = xDBLe(RX,RZ, A24, C24, e2-1)
		A24, C24 = get_2_isog(TX, TZ)
		RX, RZ = eval_2_isog(TX, TZ, RX, RZ)
		if is_points:
			phiPX, phiPZ = eval_2_isog(TX, TZ, phiPX, phiPZ) #P=phi(P)
			phiQX, phiQZ = eval_2_isog(TX, TZ, phiQX, phiQZ) #Q=phi(Q)
			phiDX, phiDZ = eval_2_isog(TX, TZ, phiDX, phiDZ) #D=phi(D)
			push = push + 3
		e2 = e2 - 1 #remove the first isogeny
		iso = iso + 1

	iso_queue = deque()
	iso_queue.append((e2/2, RX, RZ))
	i = 0

	#Alice's main loop - note that iso_queue returns True if non-empty
	while iso_queue:
		h, X, Z = iso_queue.pop()

		# Check for valid strategy
		assert h == 1 or strategy_Alice[i] < h, "Alice's strategy is invalid."

		if h == 1:
			A24, C24, consts = get_4_isog(X, Z)
			iso = iso + 1
			iso_queue_2 = deque()
			while iso_queue:
				h, X, Z = iso_queue.popleft()
				X, Z = eval_4_isog(consts, X, Z)
				iso = iso + 1
				iso_queue_2.append((h-1, X, Z))
			iso_queue = iso_queue_2
			if is_points:
				phiPX, phiPZ = eval_4_isog(consts, phiPX, phiPZ) #P=phi(P)
				phiQX, phiQZ = eval_4_isog(consts, phiQX, phiQZ) #Q=phi(Q)
				phiDX, phiDZ = eval_4_isog(consts, phiDX, phiDZ) #D=phi(D)
				push = push + 3

		else:
			iso_queue.append((h, X, Z))
			X, Z = xDBLe(X, Z, A24, C24, 2*strategy_Alice[i])
			iso_queue.append((h-strategy_Alice[i], X, Z))
			i = i+1

	if is_points:
		points = [[phiPX, phiPZ], [phiQX, phiQZ], [phiDX, phiDZ]]
	return A24, C24, points, iso, push

def iso_3_e(APLUS, AMINUS, RX, RZ, points=None):
	#inputs: curve constants (APLUS: AMINUS) where (APLUS : AMINUS) = (A + 2C : A - 2C) for projective curve (A:C) and a torsion point RX, RZ of order eB
	#optional input: a list of torsion points to push through the isogenies
	#output: image curve, and optional image of torsion points on that curve
	
	# counters
	iso, push = 0, 0

	is_points = 0 if points is None else 1

	#Number of 3-isogenies to compute
	e3 = eB

	if points:
		phiPX, phiPZ = points[0][0], points[0][1]
		phiQX, phiQZ = points[1][0], points[1][1]
		phiDX, phiDZ = points[2][0], points[2][1]

	#Bob's main loop
	for e in reversed(range(e3)):
		# multiply the kernel point by it's order less 1
		TX, TZ = xTPLe(RX,RZ, APLUS, AMINUS ,e) 
		# get the next isogeny - image curve and map parameters
		APLUS, AMINUS, consts = get_3_isog(TX, TZ)
		iso = iso + 1
		if e != 0:
			RX, RZ = eval_3_isog(consts, RX, RZ)
			
			push = push + 1
		if is_points:
			#evaluate 3-isogeny at Alice's points		
			phiPX, phiPZ = eval_3_isog(consts, phiPX, phiPZ) #P=phi(P)
			phiQX, phiQZ = eval_3_isog(consts, phiQX, phiQZ) #Q=phi(Q)
			phiDX, phiDZ = eval_3_isog(consts, phiDX, phiDZ) #D=phi(D)
			push = push + 3
	
	if is_points:
		points = [[phiPX, phiPZ], [phiQX, phiQZ], [phiDX, phiDZ]]
	return APLUS, AMINUS, points, iso, push
	
def iso_3_e_with_strategies(APLUS, AMINUS, RX, RZ, points=None):
	#inputs: curve constants (APLUS: AMINUS) where (APLUS : AMINUS) = (A + 2C : A - 2C) for projective curve (A:C) and a torsion point RX, RZ of order eB
	#optional input: a list of torsion points to push through the isogenies
	#output: image curve, and optional image of torsion points on that curve
	
	# counters
	iso, push = 0, 0

	is_points = 0 if points is None else 1

	#Number of 3-isogenies to compute
	e3 = eB

	if points:
		phiPX, phiPZ = points[0][0], points[0][1]
		phiQX, phiQZ = points[1][0], points[1][1]
		phiDX, phiDZ = points[2][0], points[2][1]

	iso_queue = deque()
	iso_queue.append((e3, RX, RZ))
	i = 0

	#Bob's main loop - note that iso_queue returns True if non-empty
	while iso_queue:
		h, X, Z = iso_queue.pop()

		# Check for valid strategy
		assert h == 1 or strategy_Bob[i] < h, "Bob's strategy is invalid."

		if h == 1:
			APLUS, AMINUS, consts = get_3_isog(X, Z)
			iso = iso + 1
			iso_queue_2 = deque()
			while iso_queue:
				h, X, Z = iso_queue.popleft()
				X, Z = eval_3_isog(consts, X, Z)
				iso = iso + 1
				iso_queue_2.append((h-1, X, Z))
			iso_queue = iso_queue_2
			if is_points:
				phiPX, phiPZ = eval_3_isog(consts, phiPX, phiPZ) #P=phi(P)
				phiQX, phiQZ = eval_3_isog(consts, phiQX, phiQZ) #Q=phi(Q)
				phiDX, phiDZ = eval_3_isog(consts, phiDX, phiDZ) #D=phi(D)
				push = push + 3
		else:
			iso_queue.append((h, X, Z))
			X, Z = xTPLe(X, Z, APLUS, AMINUS, strategy_Bob[i])
			iso_queue.append((h-strategy_Bob[i], X, Z))
			i = i+1
	
	if is_points:
		points = [[phiPX, phiPZ], [phiQX, phiQZ], [phiDX, phiDZ]]
	return APLUS, AMINUS, points, iso, push



##########################################################################

	

#KEYGEN

def keygen_Alice(SK_Alice, params_Alice, params_Bob):
	#input: secret integer SK_Alice
	#       public parameters [XPA, XQA, XRA] and [XPB, XQB, XRB]
	#output: public key [phi_A(x(PB)),phi_A(x(QB)),phi_A(x(QB-PB))] 
	
	A, C = Complex(6), Complex(1) #starting montgomery curve
	phiPX = params_Bob[0]  #Bob's starting points -> public key
	phiPZ = Complex(1)
	phiQX = params_Bob[1]
	phiQZ = Complex(1)
	phiDX, phiDZ = params_Bob[2], Complex(1)  #(phiDX:phiDZ)=x(Q-P)
	
	points = [[phiPX, phiPZ], [phiQX, phiQZ], [phiDX, phiDZ]]
	#special curve representation used for 2 isogenies (A:C) ~ (A24: C24) = (A+2C:4C)

	A24 = A+(Complex(2)*C) 
	C24 = Complex(4)*C
	#Number of 2-isogenies to compute
	e2 = eA

	#compute the point x(R)=(RX:RZ) via secre_pt, R=P+[SK_Alice]Q
	RX, RZ = LADDER_3_pt(SK_Alice, params_Alice[0], params_Alice[1], params_Alice[2], A)

	#Compute isogenies on base curve and points with kernel RX, RZ
	A24, C24, points, iso, push = iso_2_e_with_strategies(A24, C24, RX, RZ, points)
	

	phiPX, phiPZ = points[0][0], points[0][1]
	phiQX, phiQZ = points[1][0], points[1][1]
	phiDX, phiDZ = points[2][0], points[2][1]


	#compute affine x-coordinates
	phiPZ, phiQZ, phiDZ = inv_3_way(phiPZ, phiQZ, phiDZ)
	phiPX = phiPX * phiPZ
	phiQX = phiQX * phiQZ
	phiDX = phiDX * phiDZ

	#Alices's public key, values in Fp2
	PK_Alice = [phiPX, phiQX, phiDX]
	
	msg="Alice's keygen needs "+str(push)+" push through computations and "+str(iso)+" isogenies"
	print(msg)
	print('')
	keysize = len(binary(phiPX.re)) + len(binary(phiPX.im)) + len(binary(phiQX.re)) + len(binary(phiQX.im))+ len(binary(phiDX.re)) + len(binary(phiDX.im))
	msg="Keysize of Alice's public key: " + str(keysize) + " bits"
	print(msg)

	return PK_Alice

##################################################################################

def keyex_Alice(sk_Alice, pk_Bob):
	
	#Order of 2-torsion
	e2 = eA

	A, C = get_A(pk_Bob[0], pk_Bob[1], pk_Bob[2]), Complex(1)
	A24 = A + (Complex(2)*C)
	C24 = Complex(4)*C
	
	# Compute Alice's secret torsion point via Bob's pushthrough points
	SX, SZ = LADDER_3_pt(sk_Alice, pk_Bob[0], pk_Bob[1], pk_Bob[2], A)

	A24, C24, _, iso, _ = iso_2_e_with_strategies(A24, C24, SX, SZ)

	msg="Alice's key exchange needs "+str(iso)+" isogenies"
	print(msg)
	print('')

	A = (Complex(4)*A24) - (Complex(2)*C24)
	C = C24

	return j_inv(A,C)
##################################################################################

def keygen_Bob(sk_Bob, params_Bob, params_Alice):
	#input: Bob's secret key
	#       public parameters [XPA, XQA, XRA] and [XPB, XQB, XRB]
	#output: Bob's public key [phi_B(x(PA)),phi_B(x(QA)),phi_B(x(QA-PA))] 
	
	A, C = Complex(6), Complex(1) #starting montgomery curve

	phiPX, phiPZ = params_Alice[0], Complex(1)  #Alice's starting points -> public key
	phiQX, phiQZ = params_Alice[1], Complex(1)
	phiDX, phiDZ = params_Alice[2], Complex(1)  #(phiDX:phiDZ)=x(Q-P)

	points = [[phiPX, phiPZ], [phiQX, phiQZ], [phiDX, phiDZ]]

	#special curve representation used for 3 isogenies (A:C) ~ (APLUS: AMINUS) = (A+2C:A-2C)

	APLUS = A + Complex(2) * C
	AMINUS = A - Complex(2) * C

	#compute the point x(R)=(RX:RZ) via 3 pt ladder, R=P+[sk_Bob]Q
	RX, RZ = LADDER_3_pt(sk_Bob, params_Bob[0], params_Bob[1], params_Bob[2], A)
	
	APLUS, AMINUS, points, iso, push = iso_3_e_with_strategies(APLUS, AMINUS, RX, RZ, points)

	phiPX, phiPZ = points[0][0], points[0][1]
	phiQX, phiQZ = points[1][0], points[1][1]
	phiDX, phiDZ = points[2][0], points[2][1]
	
	#compute affine x-coordinates
	phiPZ, phiQZ, phiDZ = inv_3_way(phiPZ, phiQZ, phiDZ)
	phiPX = phiPX * phiPZ
	phiQX = phiQX * phiQZ
	phiDX = phiDX * phiDZ

	#Bob's public key, affine values in Fp2
	pk_Bob = [phiPX, phiQX, phiDX]
	
	msg="Bob's keygen needs "+str(push)+" push through computations and "+str(iso)+" isogenies"
	print(msg)
	print('')
	keysize = len(binary(phiPX.re)) + len(binary(phiPX.im)) + len(binary(phiQX.re)) + len(binary(phiQX.im))+ len(binary(phiDX.re)) + len(binary(phiDX.im))
	msg="Keysize of Bob's public key: " + str(keysize) + " bits"
	print(msg)

	return pk_Bob

##################################################################################

def keyex_Bob(sk_Bob, pk_Alice):
	#Order of 3-torsion
	e3 = eB

	A, C = get_A(pk_Alice[0], pk_Alice[1], pk_Alice[2]), Complex(1)

	#special curve representation used for 3 isogenies (A:C) ~ (APLUS: AMINUS) = (A+2C:A-2C)
	APLUS = A + Complex(2) * C
	AMINUS = A - Complex(2) * C
	
	# Compute Bob's secret torsion point via Alice's pushthrough points
	RX, RZ = LADDER_3_pt(sk_Bob, pk_Alice[0], pk_Alice[1], pk_Alice[2], A)

	# Compute Bob's image curve
	APLUS, AMINUS, _, iso, _ = iso_3_e_with_strategies(APLUS, AMINUS, RX, RZ)

	

	inv2 = Complex(2).inv()
	A = (APLUS + AMINUS) * inv2
	C = (APLUS - A) * inv2

	msg="Bob's key exchange needs "+str(iso)+" isogenies"
	print(msg)
	print('')

	return j_inv(A,C)

##################################################################################

# binary function needed for computing 3 pt ladder. Returns list of bits starting with lsb.
binary = lambda n: n>0 and [n&1]+binary(n>>1) or []

#parameters defining prime p=lA^eA*lB^e_B*f-1
lA=2
lB=3

#SIKEp182 field parameters
# eA=0x5b
# eB=0x39
# f=1

#SIKEp434 field parameters
eA = 0xD8
eB = 0x89
f=1

#defining p (must be prime!)
p=(lA**eA)*(lB**eB)*f-1   

#inverse of 4, needed for 3-pt-ladder
inv4 = Complex(4).inv()


#SIKEp182 point parameters
# XQA = Complex(0x27b8def415bae0506a9607fff7704832151cdcbc93cb22,0x85c86f386b94b8c413f5e49736f26de95103a9b65f31a)
# XPA = Complex(0x5a324935a4d7b75024fdc3601fe8b5888cea9f88212b2, 0x2357bdd576772bf2a93e3d680ed7306e16eafc6aff904)
# XRA = Complex(0x10dbd4618e711e211d73901505d3f42f7e18a39d54eb97,0x19419c1b078b8e0aef16db4e080f45c877dfb661cc8d31)
# XQB = Complex(0x2dcff7123e2380f552f5bff91da77ae62e9556b866d8f, 0)
# XPB = Complex(0x02ca3bc7e98f88b3ca3239c276eb7a224c51f61bc8c5ed,0)
# XRB = Complex(0x1d7368799ec7ae17ee845ca08d2463e20579d73bdacd47, 0x19667254c765d2e9dca805c9c55aec4f1c67e1eb4b61c0)

#SIKEp434 point params
XPA = Complex(0x00003CCFC5E1F050030363E6920A0F7A4C6C71E63DE63A0E6475AF621995705F7C84500CB2BB61E950E19EAB8661D25C4A50ED279646CB48, 0x0001AD1C1CAE7840EDDA6D8A924520F60E573D3B9DFAC6D189941CB22326D284A8816CC4249410FE80D68047D823C97D705246F869E3EA50)
XQA = Complex(0x0000C7461738340EFCF09CE388F666EB38F7F3AFD42DC0B664D9F461F31AA2EDC6B4AB71BD42F4D7C058E13F64B237EF7DDD2ABC0DEB0C6C, 0x000025DE37157F50D75D320DD0682AB4A67E471586FBC2D31AA32E6957FA2B2614C4CD40A1E27283EAAF4272AE517847197432E2D61C85F5)
XRA = Complex(0x0000F37AB34BA0CEAD94F43CDC50DE06AD19C67CE4928346E829CB92580DA84D7C36506A2516696BBE3AEB523AD7172A6D239513C5FD2516, 0x000196CA2ED06A657E90A73543F3902C208F410895B49CF84CD89BE9ED6E4EE7E8DF90B05F3FDB8BDFE489D1B3558E987013F9806036C5AC)
XPB = Complex(0x00008664865EA7D816F03B31E223C26D406A2C6CD0C3D667466056AAE85895EC37368BFC009DFAFCB3D97E639F65E9E45F46573B0637B7A9, 0)
XQB = Complex(0x00012E84D7652558E694BF84C1FBDAAF99B83B4266C32EC65B10457BCAF94C63EB063681E8B1E7398C0B241C19B9665FDB9E1406DA3D3846, 0)
XRB = Complex(0x0001CD28597256D4FFE7E002E87870752A8F8A64A1CC78B5A2122074783F51B4FDE90E89C48ED91A8F4A0CCBACBFA7F51A89CE518A52B76C, 0x000147073290D78DD0CC8420B1188187D1A49DBFA24F26AAD46B2D9BB547DBB6F63A760ECB0C2B20BE52FB77BD2776C3D14BCBC404736AE4)


params_Alice = [XPA, XQA, XRA]
params_Bob = [XPB, XQB, XRB]


#################################################################
#strategy paramaters - generated strategies using strategies.py for given parameters

#p182 
# strategy_Alice = [17, 12, 7, 4, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1]
# strategy_Bob = [21, 13, 8, 5, 3, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1]

#p434
strategy_Alice = [48, 28, 16, 8, 4, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8, 4, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 13, 7, 4, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 21, 12, 7, 4, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1]

strategy_Bob = [48, 34, 21, 13, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 13, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 14, 13, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1]



# #######################################################################



n_Alice = 1737702558708573667130951476
n_Bob = 12303434235345345

PK_BOB = [Complex(0x12ee31a5fa5384f9394912c0577dd4f26ff4822a7021cd, 0x2279a23745a5596215baf7f8ef4138ef521c9d62cc2f0f), Complex(0x1bb8a4d5bb611e4c8db042b00e62c6132f4abd4d9a4083, 0x1177920ed42b0d371b1133de98e51b1d0969b6cf416ec7), Complex(0x4e339959f8b6992cd2ceb9735705d42160987b2bed6a9,0x191c38fd8e71bdf9a7e5f60921a817e413cb751a291537)]


PKA = keygen_Alice(n_Alice, params_Alice,params_Bob)
print('')
print("Alice's Public Key:")
print(hex(PKA[0].re), hex(PKA[0].im))
print(hex(PKA[1].re), hex(PKA[1].im))
print(hex(PKA[2].re), hex(PKA[2].im))
print('')

PKB = keygen_Bob(n_Bob, params_Bob, params_Alice)
print('')
print("Bob's Public Key:")
print(hex(PKB[0].re), hex(PKB[0].im))
print(hex(PKB[1].re), hex(PKB[1].im))
print(hex(PKB[2].re), hex(PKB[2].im))
print('')


final_j_alice = keyex_Alice(n_Alice, PKB)


print("Alice exchanges key to obtain j-invariant: {} + {} * i".format(hex(final_j_alice.re), hex(final_j_alice.im)))
print("")

final_j_bob = keyex_Bob(n_Bob, PKA)

print("Bob exchanges key to obtain j-invariant: {} + {} * i".format(hex(final_j_bob.re), hex(final_j_bob.im)))

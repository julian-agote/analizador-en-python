#!/usr/bin/env python
import sys
class G:
	def __init__(self):
		self.P={'A':[(['P','M1','=>','FCONJ'],'nueva_premisa;demostrarArgumento'),],
			'LF':[(['coma','M1','FCONJ','LF'],''),(['lambda'],''),],
			'FIMPL':[(['G','FIMPLP'],''),],
			'G':[(['neg','G'],'introd_neg'),(['(','FCONJ',')'],'agrupar'),(['prop'],'introd_prop'),],
			'FCONJ':[(['FIMPL','FCONJP'],''),],
			'P':[(['FCONJ','LF'],''),],
			'M1':[(['lambda'],'nueva_premisa'),],
			'FIMPLP':[(['impl','M2','G','M3','FIMPLP'],''),(['coimpl','M2','G','M3','FIMPLP'],''),(['lambda'],''),],
			'M2':[(['lambda'],'guardar'),],
			'Aprima':[(['A'],''),],
			'FCONJP':[(['conj_dis','M2','FIMPL','M3','FCONJP'],''),(['lambda'],''),],
			'M3':[(['lambda'],'introd_conec'),],
			}
		self.taccion=[{'neg':('desplazar',3),'prop':('desplazar',1),'(':('desplazar',2),},
             		{'coma':('reducir',{'G':['prop']}),'=>':('reducir',{'G':['prop']}),'conj_dis':('reducir',{'G':['prop']}),'coimpl':('reducir',{'G':['prop']}),'impl':('reducir',{'G':['prop']}),},
             		{'neg':('desplazar',11),'prop':('desplazar',9),'(':('desplazar',10),},
             		{'neg':('desplazar',3),'prop':('desplazar',1),'(':('desplazar',2),},
             		{'$':('aceptar',{'Aprima':['A']}),},
             		{'=>':('reducir',{'M1':['lambda']}),},
             		{'coma':('desplazar',17),'=>':('reducir',{'LF':['lambda']}),},
             		{'coma':('reducir',{'FCONJP':['lambda']}),'=>':('reducir',{'FCONJP':['lambda']}),'conj_dis':('desplazar',19),},
             		{'coma':('reducir',{'FIMPLP':['lambda']}),'=>':('reducir',{'FIMPLP':['lambda']}),'conj_dis':('reducir',{'FIMPLP':['lambda']}),'coimpl':('desplazar',22),'impl':('desplazar',21),},
             		{')':('reducir',{'G':['prop']}),'conj_dis':('reducir',{'G':['prop']}),'coimpl':('reducir',{'G':['prop']}),'impl':('reducir',{'G':['prop']}),},
             		{'neg':('desplazar',11),'prop':('desplazar',9),'(':('desplazar',10),},
             		{'neg':('desplazar',11),'prop':('desplazar',9),'(':('desplazar',10),},
             		{')':('desplazar',26),},
             		{')':('reducir',{'FCONJP':['lambda']}),'conj_dis':('desplazar',27),},
             		{')':('reducir',{'FIMPLP':['lambda']}),'conj_dis':('reducir',{'FIMPLP':['lambda']}),'coimpl':('desplazar',30),'impl':('desplazar',29),},
             		{'coma':('reducir',{'G':['neg','G']}),'=>':('reducir',{'G':['neg','G']}),'conj_dis':('reducir',{'G':['neg','G']}),'coimpl':('reducir',{'G':['neg','G']}),'impl':('reducir',{'G':['neg','G']}),},
             		{'=>':('desplazar',32),},
             		{'neg':('reducir',{'M1':['lambda']}),'prop':('reducir',{'M1':['lambda']}),'(':('reducir',{'M1':['lambda']}),},
             		{'=>':('reducir',{'P':['FCONJ','LF']}),},
             		{'neg':('reducir',{'M2':['lambda']}),'prop':('reducir',{'M2':['lambda']}),'(':('reducir',{'M2':['lambda']}),},
             		{'coma':('reducir',{'FCONJ':['FIMPL','FCONJP']}),'=>':('reducir',{'FCONJ':['FIMPL','FCONJP']}),},
             		{'neg':('reducir',{'M2':['lambda']}),'prop':('reducir',{'M2':['lambda']}),'(':('reducir',{'M2':['lambda']}),},
             		{'neg':('reducir',{'M2':['lambda']}),'prop':('reducir',{'M2':['lambda']}),'(':('reducir',{'M2':['lambda']}),},
             		{'coma':('reducir',{'FIMPL':['G','FIMPLP']}),'=>':('reducir',{'FIMPL':['G','FIMPLP']}),'conj_dis':('reducir',{'FIMPL':['G','FIMPLP']}),},
             		{')':('desplazar',37),},
             		{')':('reducir',{'G':['neg','G']}),'conj_dis':('reducir',{'G':['neg','G']}),'coimpl':('reducir',{'G':['neg','G']}),'impl':('reducir',{'G':['neg','G']}),},
             		{'coma':('reducir',{'G':['(','FCONJ',')']}),'=>':('reducir',{'G':['(','FCONJ',')']}),'conj_dis':('reducir',{'G':['(','FCONJ',')']}),'coimpl':('reducir',{'G':['(','FCONJ',')']}),'impl':('reducir',{'G':['(','FCONJ',')']}),},
             		{'neg':('reducir',{'M2':['lambda']}),'prop':('reducir',{'M2':['lambda']}),'(':('reducir',{'M2':['lambda']}),},
             		{')':('reducir',{'FCONJ':['FIMPL','FCONJP']}),},
             		{'neg':('reducir',{'M2':['lambda']}),'prop':('reducir',{'M2':['lambda']}),'(':('reducir',{'M2':['lambda']}),},
             		{'neg':('reducir',{'M2':['lambda']}),'prop':('reducir',{'M2':['lambda']}),'(':('reducir',{'M2':['lambda']}),},
             		{')':('reducir',{'FIMPL':['G','FIMPLP']}),'conj_dis':('reducir',{'FIMPL':['G','FIMPLP']}),},
             		{'neg':('desplazar',43),'prop':('desplazar',41),'(':('desplazar',42),},
             		{'neg':('desplazar',3),'prop':('desplazar',1),'(':('desplazar',2),},
             		{'neg':('desplazar',3),'prop':('desplazar',1),'(':('desplazar',2),},
             		{'neg':('desplazar',3),'prop':('desplazar',1),'(':('desplazar',2),},
             		{'neg':('desplazar',3),'prop':('desplazar',1),'(':('desplazar',2),},
             		{')':('reducir',{'G':['(','FCONJ',')']}),'conj_dis':('reducir',{'G':['(','FCONJ',')']}),'coimpl':('reducir',{'G':['(','FCONJ',')']}),'impl':('reducir',{'G':['(','FCONJ',')']}),},
             		{'neg':('desplazar',11),'prop':('desplazar',9),'(':('desplazar',10),},
             		{'neg':('desplazar',11),'prop':('desplazar',9),'(':('desplazar',10),},
             		{'neg':('desplazar',11),'prop':('desplazar',9),'(':('desplazar',10),},
             		{'conj_dis':('reducir',{'G':['prop']}),'coimpl':('reducir',{'G':['prop']}),'impl':('reducir',{'G':['prop']}),'$':('reducir',{'G':['prop']}),},
             		{'neg':('desplazar',11),'prop':('desplazar',9),'(':('desplazar',10),},
             		{'neg':('desplazar',43),'prop':('desplazar',41),'(':('desplazar',42),},
             		{'$':('reducir',{'A':['P','M1','=>','FCONJ']}),},
             		{'conj_dis':('desplazar',56),'$':('reducir',{'FCONJP':['lambda']}),},
             		{'conj_dis':('reducir',{'FIMPLP':['lambda']}),'coimpl':('desplazar',59),'impl':('desplazar',58),'$':('reducir',{'FIMPLP':['lambda']}),},
             		{'coma':('desplazar',17),'=>':('reducir',{'LF':['lambda']}),},
             		{'coma':('reducir',{'M3':['lambda']}),'=>':('reducir',{'M3':['lambda']}),'conj_dis':('reducir',{'M3':['lambda']}),},
             		{'coma':('reducir',{'M3':['lambda']}),'=>':('reducir',{'M3':['lambda']}),'conj_dis':('reducir',{'M3':['lambda']}),'coimpl':('reducir',{'M3':['lambda']}),'impl':('reducir',{'M3':['lambda']}),},
             		{'coma':('reducir',{'M3':['lambda']}),'=>':('reducir',{'M3':['lambda']}),'conj_dis':('reducir',{'M3':['lambda']}),'coimpl':('reducir',{'M3':['lambda']}),'impl':('reducir',{'M3':['lambda']}),},
             		{')':('reducir',{'M3':['lambda']}),'conj_dis':('reducir',{'M3':['lambda']}),},
             		{')':('reducir',{'M3':['lambda']}),'conj_dis':('reducir',{'M3':['lambda']}),'coimpl':('reducir',{'M3':['lambda']}),'impl':('reducir',{'M3':['lambda']}),},
             		{')':('reducir',{'M3':['lambda']}),'conj_dis':('reducir',{'M3':['lambda']}),'coimpl':('reducir',{'M3':['lambda']}),'impl':('reducir',{'M3':['lambda']}),},
             		{')':('desplazar',68),},
             		{'conj_dis':('reducir',{'G':['neg','G']}),'coimpl':('reducir',{'G':['neg','G']}),'impl':('reducir',{'G':['neg','G']}),'$':('reducir',{'G':['neg','G']}),},
             		{'neg':('reducir',{'M2':['lambda']}),'prop':('reducir',{'M2':['lambda']}),'(':('reducir',{'M2':['lambda']}),},
             		{'$':('reducir',{'FCONJ':['FIMPL','FCONJP']}),},
             		{'neg':('reducir',{'M2':['lambda']}),'prop':('reducir',{'M2':['lambda']}),'(':('reducir',{'M2':['lambda']}),},
             		{'neg':('reducir',{'M2':['lambda']}),'prop':('reducir',{'M2':['lambda']}),'(':('reducir',{'M2':['lambda']}),},
             		{'conj_dis':('reducir',{'FIMPL':['G','FIMPLP']}),'$':('reducir',{'FIMPL':['G','FIMPLP']}),},
             		{'=>':('reducir',{'LF':['coma','M1','FCONJ','LF']}),},
             		{'coma':('reducir',{'FCONJP':['lambda']}),'=>':('reducir',{'FCONJP':['lambda']}),'conj_dis':('desplazar',19),},
             		{'coma':('reducir',{'FIMPLP':['lambda']}),'=>':('reducir',{'FIMPLP':['lambda']}),'conj_dis':('reducir',{'FIMPLP':['lambda']}),'coimpl':('desplazar',22),'impl':('desplazar',21),},
             		{'coma':('reducir',{'FIMPLP':['lambda']}),'=>':('reducir',{'FIMPLP':['lambda']}),'conj_dis':('reducir',{'FIMPLP':['lambda']}),'coimpl':('desplazar',22),'impl':('desplazar',21),},
             		{')':('reducir',{'FCONJP':['lambda']}),'conj_dis':('desplazar',27),},
             		{')':('reducir',{'FIMPLP':['lambda']}),'conj_dis':('reducir',{'FIMPLP':['lambda']}),'coimpl':('desplazar',30),'impl':('desplazar',29),},
             		{')':('reducir',{'FIMPLP':['lambda']}),'conj_dis':('reducir',{'FIMPLP':['lambda']}),'coimpl':('desplazar',30),'impl':('desplazar',29),},
             		{'conj_dis':('reducir',{'G':['(','FCONJ',')']}),'coimpl':('reducir',{'G':['(','FCONJ',')']}),'impl':('reducir',{'G':['(','FCONJ',')']}),'$':('reducir',{'G':['(','FCONJ',')']}),},
             		{'neg':('desplazar',43),'prop':('desplazar',41),'(':('desplazar',42),},
             		{'neg':('desplazar',43),'prop':('desplazar',41),'(':('desplazar',42),},
             		{'neg':('desplazar',43),'prop':('desplazar',41),'(':('desplazar',42),},
             		{'coma':('reducir',{'FCONJP':['conj_dis','M2','FIMPL','M3','FCONJP']}),'=>':('reducir',{'FCONJP':['conj_dis','M2','FIMPL','M3','FCONJP']}),},
             		{'coma':('reducir',{'FIMPLP':['impl','M2','G','M3','FIMPLP']}),'=>':('reducir',{'FIMPLP':['impl','M2','G','M3','FIMPLP']}),'conj_dis':('reducir',{'FIMPLP':['impl','M2','G','M3','FIMPLP']}),},
             		{'coma':('reducir',{'FIMPLP':['coimpl','M2','G','M3','FIMPLP']}),'=>':('reducir',{'FIMPLP':['coimpl','M2','G','M3','FIMPLP']}),'conj_dis':('reducir',{'FIMPLP':['coimpl','M2','G','M3','FIMPLP']}),},
             		{')':('reducir',{'FCONJP':['conj_dis','M2','FIMPL','M3','FCONJP']}),},
             		{')':('reducir',{'FIMPLP':['impl','M2','G','M3','FIMPLP']}),'conj_dis':('reducir',{'FIMPLP':['impl','M2','G','M3','FIMPLP']}),},
             		{')':('reducir',{'FIMPLP':['coimpl','M2','G','M3','FIMPLP']}),'conj_dis':('reducir',{'FIMPLP':['coimpl','M2','G','M3','FIMPLP']}),},
             		{'conj_dis':('reducir',{'M3':['lambda']}),'$':('reducir',{'M3':['lambda']}),},
             		{'conj_dis':('reducir',{'M3':['lambda']}),'coimpl':('reducir',{'M3':['lambda']}),'impl':('reducir',{'M3':['lambda']}),'$':('reducir',{'M3':['lambda']}),},
             		{'conj_dis':('reducir',{'M3':['lambda']}),'coimpl':('reducir',{'M3':['lambda']}),'impl':('reducir',{'M3':['lambda']}),'$':('reducir',{'M3':['lambda']}),},
             		{'conj_dis':('desplazar',56),'$':('reducir',{'FCONJP':['lambda']}),},
             		{'conj_dis':('reducir',{'FIMPLP':['lambda']}),'coimpl':('desplazar',59),'impl':('desplazar',58),'$':('reducir',{'FIMPLP':['lambda']}),},
             		{'conj_dis':('reducir',{'FIMPLP':['lambda']}),'coimpl':('desplazar',59),'impl':('desplazar',58),'$':('reducir',{'FIMPLP':['lambda']}),},
             		{'$':('reducir',{'FCONJP':['conj_dis','M2','FIMPL','M3','FCONJP']}),},
             		{'conj_dis':('reducir',{'FIMPLP':['impl','M2','G','M3','FIMPLP']}),'$':('reducir',{'FIMPLP':['impl','M2','G','M3','FIMPLP']}),},
             		{'conj_dis':('reducir',{'FIMPLP':['coimpl','M2','G','M3','FIMPLP']}),'$':('reducir',{'FIMPLP':['coimpl','M2','G','M3','FIMPLP']}),},
             		]
		self.tir_a=[{'A':4,'FCONJ':6,'FIMPL':7,'G':8,'(':2,'prop':1,'P':5,'neg':3,},
            		{},
            		{'FCONJ':12,'FIMPL':13,'G':14,'(':10,'prop':9,'neg':11,},
            		{'(':2,'G':15,'neg':3,'prop':1,},
            		{},
            		{'M1':16,},
            		{'coma':17,'LF':18,},
            		{'FCONJP':20,'conj_dis':19,},
            		{'FIMPLP':23,'coimpl':22,'impl':21,},
            		{},
            		{'FCONJ':24,'FIMPL':13,'G':14,'(':10,'prop':9,'neg':11,},
            		{'(':10,'G':25,'neg':11,'prop':9,},
            		{')':26,},
            		{'FCONJP':28,'conj_dis':27,},
            		{'FIMPLP':31,'coimpl':30,'impl':29,},
            		{},
            		{'=>':32,},
            		{'M1':33,},
            		{},
            		{'M2':34,},
            		{},
            		{'M2':35,},
            		{'M2':36,},
            		{},
            		{')':37,},
            		{},
            		{},
            		{'M2':38,},
            		{},
            		{'M2':39,},
            		{'M2':40,},
            		{},
            		{'FCONJ':44,'FIMPL':45,'G':46,'(':42,'prop':41,'neg':43,},
            		{'FCONJ':47,'FIMPL':7,'G':8,'(':2,'prop':1,'neg':3,},
            		{'G':8,'(':2,'FIMPL':48,'neg':3,'prop':1,},
            		{'(':2,'G':49,'neg':3,'prop':1,},
            		{'(':2,'G':50,'neg':3,'prop':1,},
            		{},
            		{'G':14,'(':10,'FIMPL':51,'neg':11,'prop':9,},
            		{'(':10,'G':52,'neg':11,'prop':9,},
            		{'(':10,'G':53,'neg':11,'prop':9,},
            		{},
            		{'FCONJ':54,'FIMPL':13,'G':14,'(':10,'prop':9,'neg':11,},
            		{'(':42,'G':55,'neg':43,'prop':41,},
            		{},
            		{'FCONJP':57,'conj_dis':56,},
            		{'FIMPLP':60,'coimpl':59,'impl':58,},
            		{'coma':17,'LF':61,},
            		{'M3':62,},
            		{'M3':63,},
            		{'M3':64,},
            		{'M3':65,},
            		{'M3':66,},
            		{'M3':67,},
            		{')':68,},
            		{},
            		{'M2':69,},
            		{},
            		{'M2':70,},
            		{'M2':71,},
            		{},
            		{},
            		{'FCONJP':72,'conj_dis':19,},
            		{'FIMPLP':73,'coimpl':22,'impl':21,},
            		{'FIMPLP':74,'coimpl':22,'impl':21,},
            		{'FCONJP':75,'conj_dis':27,},
            		{'FIMPLP':76,'coimpl':30,'impl':29,},
            		{'FIMPLP':77,'coimpl':30,'impl':29,},
            		{},
            		{'G':46,'(':42,'FIMPL':78,'neg':43,'prop':41,},
            		{'(':42,'G':79,'neg':43,'prop':41,},
            		{'(':42,'G':80,'neg':43,'prop':41,},
            		{},
            		{},
            		{},
            		{},
            		{},
            		{},
            		{'M3':81,},
            		{'M3':82,},
            		{'M3':83,},
            		{'FCONJP':84,'conj_dis':56,},
            		{'FIMPLP':85,'coimpl':59,'impl':58,},
            		{'FIMPLP':86,'coimpl':59,'impl':58,},
            		{},
            		{},
            		{},
            		]
		self.f = open(sys.argv[1],'r')
	def LeerSigTerm(self):
		CarSgte = self.f.read(1)
		while(CarSgte in [' ','\t','\n']):
			CarSgte = self.f.read(1)
		if CarSgte=='':
			return ('$','$')
		lexema= CarSgte
		if CarSgte in ('(',')','='):
			token = CarSgte
			if CarSgte=='=':
				CarSgte = self.f.read(1)
				token += CarSgte
				lexema += CarSgte
		elif CarSgte == ',':
			token = 'coma'
		elif CarSgte == '~':
			token = 'neg'
		elif CarSgte in ('^','v'):
			token = 'conj_dis'
		elif CarSgte =='-':
			CarSgte = self.f.read(1)
			lexema += CarSgte
			token = 'impl' 			
		elif CarSgte =='<':
			CarSgte = self.f.read(1)
			lexema += CarSgte
			CarSgte = self.f.read(1)
			lexema += CarSgte
			token = 'coimpl' 			
		elif CarSgte in [chr(i) for i in range(ord('a'),ord('z'))]+['z']+[chr(i) for i in range(ord('A'),ord('Z'))]+['Z']:
			token = 'prop'
		return (token,lexema)
	def parserAscendente(self):
		pila=[0]
		a,l = self.LeerSigTerm()
		while True:
			estado=pila[-1]
			if not a in self.taccion[estado].keys():
				print 'Error, falta entrada en accion, estado ',estado,' con ',a
				return False
			else:
				op,r=self.taccion[estado][a]
				if op=='reducir':
					#sacar tantos elementos de la pila como simbolos hay en la parte dcha. de la regla de reduccion
					k=r.keys()
					if r[k[0]]!=['lambda']:
						for i in range(len(r[k[0]])):
							pila.pop()
					#meter en la pila el estado que corresponde a introducir la vble de la parte izda. de la regla
					if k[0] not in self.tir_a[pila[-1]]:
						print 'Error:falta el estado al cual ir despues de reducir ',pila[-1],' con ',k[0]
						return False
					pila.append(self.tir_a[pila[-1]][k[0]])
					#ejecutar la accion semantica correspondiente a la regla reducida
					for n,v in self.P.iteritems():
						if n==k[0]:
							for x in v:
								p,acc_sem=x
								if r[k[0]]==p and acc_sem:
									print 'Ejecutar ',acc_sem
				elif op=='desplazar':
					pila.append(r)
					a,l = self.LeerSigTerm()
				elif op=='aceptar' and a=='$':
					return True
				else:
					print 'Error: la entrada continua y se ha llegado a un estado de aceptacion'
					return False
Glflp = G()
Glflp.parserAscendente()

#!/usr/bin/env python
import sys
def concatenar(s1,s2):
	return s1+' '+s2
class G:
	def __init__(self):
		self.T = ['prop','(',')','coma','=>','conj_dis','impl','coimpl','neg']
		self.V = ['A','P','LF','FCONJ','FCONJP','FIMPL','FIMPLP','G']
		self.S = 'A'
		self.P = {'A':['P nueva_premisa => FCONJ nueva_premisa demostrarArgumento'.split()],
	                'P':['FCONJ LF'.split()],
	                'LF':['coma nueva_premisa FCONJ LF'.split(),['lambda']],
	                'FCONJ':['FIMPL FCONJP'.split()],
	                'FCONJP':['conj_dis guardar FIMPL introd_conec FCONJP'.split(),['lambda']],
	                'FIMPL':['G FIMPLP'.split()],
	                'FIMPLP':['impl guardar G introd_conec FIMPLP'.split(),'coimpl guardar G introd_conec FIMPLP'.split(),['lambda']],
	                'G':['neg G introd_neg'.split(),'( FCONJ ) agrupar'.split(),'prop introd_prop'.split()]}
		self.Primero = {};
		self.Siguiente = {};
		self.M = {}  # es la tabla de analisis sintactico M[A,a] en la que se indica la regla a aplicar partiendo del
		             # no terminal A cuando el siguiente simbolo de la entrada es a
		self.f = open(sys.argv[1],'r')
		self.acciones_sem = ['introd_conec','introd_neg','introd_prop','agrupar','nueva_premisa',
					   'guardar','obtenerTablaVerdad','demostrarArgumento']
		self.pila_sem =[]
		self.arbol=[]
		self.premisas=[]
		self.posicion={} # para saber a cada prop. que posicion le corresponde en el array de V,F
		self.posicion_aux={}
		self.estado=[]   # para ir guardando los sucesivos valores de verdad de las proposiciones
	def CalcularPrimero(self):
		for I in self.T:
			self.Primero[I] = [I]
		for X in self.V:
			for r in self.P[X]:
				if r[0]=='lambda':
					self.Primero[X] = ['lambda']
		Final = False
		while not Final:
			Final = True
			for X in self.V:
				for alfa in self.P[X]:
					cadena = alfa
					YaEsta = False
					while not YaEsta and len(cadena)>0:
						Y = cadena[0]
						while Y in self.acciones_sem and len(cadena):
							cadena=cadena[1:]
							if len(cadena):
								Y=cadena[0]
							else:
								Y=''
						if not Y:
							break
						YaEsta = True
						if X in self.Primero:
							longi = len(self.Primero[X])
						else:
							longi = 0
						if Y in self.Primero:		
							for Z in self.Primero[Y]:
								if Z != 'lambda':
									if X in self.Primero:
										if not self.Primero[X].count(Z):
											self.Primero[X].append(Z)
									else:
										self.Primero[X] = [Z]
								else:
									cadena = cadena[1:]
									YaEsta = False
							if X in self.Primero:
								if longi < len(self.Primero[X]):
									Final = False
					if len(cadena)==0:
						if X in self.Primero:
							if not self.Primero[X].count('lambda'):
								self.Primero[X].append('lambda')
								Final = False
						else:
							self.Primero[X] = ['lambda'] 
							Final = False
	def MostrarPrimero(self):
		for k,v in self.Primero.iteritems():
			print 'Primero(',k,')=',v
	# Se define Primero(alfa) siendo alfa una cadena cualquiera de simbolos de la gramatica como el cjto. de todos los
	# terminales que inician alguna cadena derivada de alfa. Si alguna derivacion de alfa produce Lambda tambien Lambda 
	# pertenece a Primero(alfa)
	def CalcularPrimeroCad(self,alfa):
		cadena = alfa
		YaEsta = False
		PrimeroCad = []
		while len(cadena) and not YaEsta:
			Y = cadena[0]
			while Y in self.acciones_sem and len(cadena):
				cadena=cadena[1:]
				if len(cadena):
					Y=cadena[0]
				else:
					Y=''
			if not Y:
				break
			if Y == 'lambda':
				break
			YaEsta = True
			for Z in self.Primero[Y]:
				if Z != 'lambda':
					if not Z in PrimeroCad:
						PrimeroCad.append(Z)
				else:
					YaEsta = False
					cadena = cadena[1:]
		if not YaEsta:
			PrimeroCad.append('lambda')
		return PrimeroCad
	# se define Siguiente(A) para el no terminal A como el cjto. de terminales que pueden aparecer a la dcha de A
	# en alguna forma sentencial derivada del axioma de la gramatica
	def CalcularSiguiente(self):
		self.Siguiente = dict([(I,[]) for I in self.V])
		self.Siguiente[self.S] = ['$']
		Final = False
		while not Final:
			Final = True
			for A in self.P.keys():
				for r in self.P[A]:
					for k in range(len(r)):
						if r[k] in self.V:
							B = r[k]
							beta = r[k+1:]
							Longi = len(self.Siguiente[B])
							if len(beta):
								PrimeroBeta = self.CalcularPrimeroCad(beta)
								for Z in PrimeroBeta:
									if Z != 'lambda':
										if not Z in self.Siguiente[B]:
											self.Siguiente[B].append(Z)
								if 'lambda' in PrimeroBeta:
									for Z in self.Siguiente[A]:
										if not Z in self.Siguiente[B]:
											self.Siguiente[B].append(Z)
							else:
								for Z in self.Siguiente[A]:
									if not Z in self.Siguiente[B]:
										self.Siguiente[B].append(Z)
							if Longi < len(self.Siguiente[B]):
								Final = False
	def MostrarSiguiente(self):
		print "=" * 20
		for k,v in self.Siguiente.iteritems():
			print 'Siguiente(',k,')=',v
	# si existe una regla A->alfa el analizador sintactico debe expandir por esta regla si en la cadena de entrada el
	# simbolo en curso pertenece a Primero(alfa). Si alfa=Lambda o deriva en Lambda (Lambda pertenece a Primero(alfa))
	# entonces se expandira por esta regla si el simbolo en curso de la entrada pertenece a siguiente(A)
	def CrearTablaAnSin(self):
		self.CalcularPrimero()
		self.CalcularSiguiente()
		self.M = dict([(I,dict([(J,[]) for J in self.T+['$']])) for I in self.V])		
		for A in self.P.keys():
			for alfa in self.P[A]:
				PrimeroAlfa = self.CalcularPrimeroCad(alfa)
				for Term in PrimeroAlfa:
					if Term != 'lambda':
						if len(self.M[A][Term])==0:
							self.M[A][Term] = alfa
						else:
							print "Error:ya existia entrada en la tabla para %s,%s" %(A,Term)
				if 'lambda' in PrimeroAlfa:
					for Term in self.Siguiente[A]:
						if len(self.M[A][Term])==0:
							self.M[A][Term] = alfa
						else:
							print "Error:ya existia entrada en la tabla para %s,%s" %(A,Term)
	def displayarTablaAnSin(self):
		f = open("tabla_LFLP.html","w")
		f.write("<!doctype html PUBLIC \"-//W3C//DTD HTML 4.0 Transitional//EN\">\n")
		f.write("<html><head><title>Tabla de Analisis del lenguaje formal de logica proposicional</title>\n")
		f.write("</head><body bgcolor=\"#f0f0f8\">\n<p>\n")
		f.write("<table border=\"1\">\n")
		f.write("<tr align=\"center\"><th>&nbsp;</th>")
		for i in self.T+['$']:
			f.write("<th>%s</th>" % i)
		for k in self.V:
			f.write("<tr align=\"center\"><td>%s</td>" % k)
			for j in self.T+['$']:
				if self.M[k][j]:
					f.write("<td>%s</td>" % reduce(concatenar,self.M[k][j]))
				else:
					f.write("<td>&nbsp;</td>")
			f.write("</tr>\n")
		f.write("</table>\n")
		f.write("</body></html>")
		f.close()	
	def guardar(self,token,lexema):
		self.pila_sem.append((token,lexema))
	def introd_conec(self):
		ld = self.pila_sem.pop()
		oper,tipo = self.pila_sem.pop() 
		li = self.pila_sem.pop()
		nodo = {'op':oper,'tipo':tipo,'li':li,'ld':ld}
		self.arbol.append(nodo)
		self.pila_sem.append(self.arbol.index(nodo))
	def introd_prop(self,lexema):
		nodo = {'op':'prop','tipo':lexema,'li':None,'ld':None}
		self.arbol.append(nodo)
		if not self.posicion.has_key(lexema):
			self.posicion[lexema]=len(self.posicion)
		self.pila_sem.append(len(self.arbol)-1)
	def introd_neg(self):
		li = self.pila_sem.pop()
		nodo = {'op':'neg','tipo':None,'li':li,'ld':None}
		self.arbol.append(nodo)
		self.pila_sem.append(self.arbol.index(nodo))
	def agrupar(self):
		li = self.pila_sem.pop()
		nodo = {'op':'agrup','tipo':None,'li':li,'ld':None}
		self.arbol.append(nodo)
		self.pila_sem.append(self.arbol.index(nodo))
	def nueva_premisa(self):
		li = self.pila_sem.pop()
		self.premisas.append(li)
	def mostrarFBC(self,i):
		if self.arbol[i]['op'] in ('conj_dis','impl','coimpl'):
			return (self.mostrarFBC(self.arbol[i]['li'])+self.arbol[i]['tipo']+self.mostrarFBC(self.arbol[i]['ld']))
		elif self.arbol[i]['op']=='neg':
			return ('~'+self.mostrarFBC(self.arbol[i]['li']))
		elif self.arbol[i]['op']=='agrup':
			return ('('+self.mostrarFBC(self.arbol[i]['li'])+')')
		elif self.arbol[i]['op']=='prop':
			return self.arbol[i]['tipo']
	def displayarArgumento(self):
		f = open("tabla_argumento.html","w")
		f.write("<!doctype html PUBLIC \"-//W3C//DTD HTML 4.0 Transitional//EN\">\n")
		f.write("<html><head><title>Tabla de Verdad del argumento</title>\n")
		f.write("</head><body bgcolor=\"#f0f0f8\">\n<p>\n")
		f.write("<table border=\"1\">\n")
		f.write("<tr align=\"center\">")
		for i in self.premisas:
			f.write("<th>%s</th>" % self.mostrarFBC(i))
		f.write("</table>\n")
		f.write("</body></html>")
		f.close()
	def calcular_fbc(self,i):
		if self.arbol[i]['op']=='neg':
			return not self.calcular_fbc(self.arbol[i]['li'])
		elif self.arbol[i]['op'] in ('conj_dis','impl','coimpl'):
			if self.arbol[i]['tipo'] == '^':
				return (self.calcular_fbc(self.arbol[i]['li']) and
					 self.calcular_fbc(self.arbol[i]['ld']))
			elif self.arbol[i]['tipo'] == 'v':
				return (self.calcular_fbc(self.arbol[i]['li']) or
					 self.calcular_fbc(self.arbol[i]['ld']))
			elif self.arbol[i]['tipo']=='->':
				if (self.calcular_fbc(self.arbol[i]['li']) and not
				   self.calcular_fbc(self.arbol[i]['ld'])):
					return False
				else:
					return True
			elif self.arbol[i]['tipo']=='<->':
				if self.calcular_fbc(self.arbol[i]['li'])==self.calcular_fbc(self.arbol[i]['ld']):
					return True
				else:
					return False
		elif self.arbol[i]['op']=='agrup':
			return self.calcular_fbc(self.arbol[i]['li'])
		elif self.arbol[i]['op']=='prop':
			return self.estado[self.posicion[self.arbol[i]['tipo']]]
	def recorrido(self,i):
		# recorre el arbol buscando las proposiciones de la formula i
		if self.arbol[i]['op']=='prop':
			if not self.posicion_aux.has_key(self.arbol[i]['tipo']):
				self.posicion_aux[self.arbol[i]['tipo']]=len(self.posicion_aux)
		elif self.arbol[i]['op'] in ('conj_dis','impl','coimpl'):
			self.recorrido(self.arbol[i]['li'])
			self.recorrido(self.arbol[i]['ld'])
		else:
			self.recorrido(self.arbol[i]['li'])
	def contradiccion(self,p_i):
		self.posicion_aux={}
		self.recorrido(p_i)
		mem_posicion=self.posicion
		self.posicion=self.posicion_aux
		self.estado=[]
		for i in range(len(self.posicion_aux)):
			self.estado.append(False)
		if self.calcular_fbc(p_i):
			self.posicion=mem_posicion
			return False
		while True:
			# obtener los sucesivos valores de verdad de las proposiciones
			for i in range(len(self.posicion_aux)):
				if not self.estado[i]:
					self.estado[i]= True
					for j in range(i):
						self.estado[j]=False
					break
			if self.calcular_fbc(p_i):
				self.posicion=mem_posicion
				return False # al menos para una combinacion la formula es verdadera
			final=True
			for i in range(len(self.posicion_aux)):
				if not self.estado[i]:
					final=False
			if final:
				break
		self.posicion=mem_posicion
		return True # devuelve True si han resultado falsas todas las entradas de la tabla de verdad de p_i					
	def obtenerTablaVerdad(self):
		f = open("TV"+sys.argv[1][:-4]+".html","w")
		f.write("<!doctype html PUBLIC \"-//W3C//DTD HTML 4.0 Transitional//EN\">\n")
		f.write("<html><head><title>Tabla de Verdad del argumento</title>\n")
		f.write("</head><body bgcolor=\"#f0f0f8\">\n<p>\n")
		f.write("<table border=\"1\">\n")
		f.write("<tr align=\"center\">")
		for i in sorted(self.posicion.keys()):
			f.write("<th>%s</th>" % i)
		for i in self.premisas:
			f.write("<th>%s</th>" % self.mostrarFBC(i))
		valido = True
		for i in range(len(self.posicion)):
			self.estado.append(False)
		f.write("<tr align=\"center\">")
		for i in sorted(self.posicion.keys()):
			f.write("<td>F</td>")
		# hallar los valores de las fbc
		for i in self.premisas:
			if self.calcular_fbc(i):
				f.write("<td>V</td>")
			else:
				f.write("<td>F</td>")
		f.write("</tr>\n")
		# ver si hay alguna combinacion en la que las premisas son verdaderas y la conclusion falsa
		if (self.premisas[:-1]==filter(self.calcular_fbc,self.premisas[:-1]) and
		   not self.calcular_fbc(self.premisas[-1])):
			valido = False
		while True:
			# obtener los sucesivos valores de verdad de las proposiciones
			for i in range(len(self.posicion)):
				if not self.estado[i]:
					self.estado[i]= True
					for j in range(i):
						self.estado[j]=False
					break
			f.write("<tr align=\"center\">")
			for i in sorted(self.posicion.keys()):
				if self.estado[self.posicion[i]]:
					f.write("<td>V</td>")
				else:
					f.write("<td>F</td>")
			# hallar los valores de las fbc
			for i in self.premisas:
				if self.calcular_fbc(i):
					f.write("<td>V</td>")
				else:
					f.write("<td>F</td>")
			f.write("</tr>\n")
			# ver si hay alguna combinacion en la que las premisas son verdaderas y la conclusion falsa
			if (self.premisas[:-1]==filter(self.calcular_fbc,self.premisas[:-1]) and
			   not self.calcular_fbc(self.premisas[-1])):
				valido = False
			final=True
			for i in range(len(self.posicion)):
				if not self.estado[i]:
					final=False
			if final:
				break
			
		f.write("</table>\n")
		f.write("</body></html>")
		f.close()	
		if valido:
			print "Es un argumento valido\n"
		else:
			print "No es un argumento valido\n"
	def iguales(self,i,j):
		if self.arbol[i]['op']=='agrup':
			return self.iguales(self.arbol[i]['li'],j)
		if self.arbol[j]['op']=='agrup':
			return self.iguales(i,self.arbol[j]['li'])
		if self.arbol[i]['op']!=self.arbol[j]['op']:
			return False
		elif self.arbol[i]['tipo']!=self.arbol[j]['tipo']:
			return False
		elif self.arbol[i]['op']=='prop':
			return True
		elif self.arbol[i]['op'] in ('conj_dis','impl','coimpl'):
			return (self.iguales(self.arbol[i]['li'],self.arbol[j]['li']) and
				  self.iguales(self.arbol[i]['ld'],self.arbol[j]['ld']))
		else:
			return self.iguales(self.arbol[i]['li'],self.arbol[j]['li'])
	def demostrarArgumento(self,reduccionAbsurdo=False):
		formulas=[]
		for i,v in enumerate(self.premisas[:-1]):
			print "(%d) " % (i+1),self.mostrarFBC(v),"\n"
			formulas.append({'ind':v,'regla':'Premisa','oper':None})
		c=len(self.premisas)
		if reduccionAbsurdo:
			self.arbol.append({'op':'neg','tipo':None,'li':self.premisas[-1],'ld':None})
			print "(%d) " % c,self.mostrarFBC(len(self.arbol)-1),"\n"
			formulas.append({'ind':len(self.arbol)-1,'regla':'PA','oper':None})
			c+=1
		# obtener mediante reglas de inferencia el resto de formulas hasta obtener la conclusion
		# las nuevas formulas se van anadiendo al arbol junto con la indicacion de la regla utilizada y con que formulas
		hay_disyuncion=None
		while True:
			final=True
			nformulas=len(formulas)
			for i,v in enumerate(formulas[:]):
				# regla de eliminacion de la conjuncion
				if (self.arbol[v['ind']]['op']=='conj_dis' and
				    self.arbol[v['ind']]['tipo']=='^' and
				    v['regla']!='RI^'):
				   	# si la nueva formula empieza por parentesis quitarlos
					if self.arbol[self.arbol[v['ind']]['li']]['op']=='agrup':
						ind=self.arbol[self.arbol[v['ind']]['li']]['li']
					else:
						ind=self.arbol[v['ind']]['li']
					# anteriormente se ha aplicado la misma regla?
					if formulas.count({'ind':ind,'regla':'RE^','oper':((i+1),)})==0:
						# si es verdad la conjuncion de dos formulas tb. lo sera cada una por separado
						formulas.append({'ind':ind,'regla':'RE^','oper':((i+1),)})
						print "(%d) " % c,self.mostrarFBC(ind),"RE^ (%d)\n" % (i+1)
						final=False
						if self.iguales(self.premisas[-1],formulas[-1]['ind']):
							final=True
							break
						# si la nueva formula empieza por parentesis quitarlos
						if self.arbol[self.arbol[v['ind']]['ld']]['op']=='agrup':
							ind=self.arbol[self.arbol[v['ind']]['ld']]['li']
						else:
							ind=self.arbol[v['ind']]['ld']
						formulas.append({'ind':ind,'regla':'RE^','oper':((i+1),)})
						print "(%d) " % (c+1),self.mostrarFBC(ind),"RE^ (%d)\n" % (i+1)
						c+=2					
				# regla de eliminacion de la implicacion 
				elif self.arbol[v['ind']]['op']=='impl':
					# ver si existe una formula que coincide con self.arbol[v['ind']]['li'] (modus ponens)
					vj=[]
					for xj,u in enumerate(formulas[:]):
						if i!=xj and (v['ind']==u['ind'] or self.iguales(u['ind'],self.arbol[v['ind']]['li'])):
							vj.append(xj)
					for j in vj:
						if self.arbol[self.arbol[v['ind']]['ld']]['op']=='agrup':
							ind=self.arbol[self.arbol[v['ind']]['ld']]['li']
						else:
							ind=self.arbol[v['ind']]['ld']
						if formulas.count({'ind':ind,'regla':'RE->','oper':((i+1),(j+1))})==0:
							# si una implicacion es verdadera y tambien lo es su antecedente podemos deducir su consecuente
							formulas.append({'ind':ind,'regla':'RE->','oper':((i+1),(j+1))})
							print "(%d) " % c,self.mostrarFBC(ind),"RE-> (%d) (%d)\n" % ((i+1),(j+1))
							c+=1
							final=False
					#ver si existe una formula con la negacion del consecuente, para asi deducir
					# la negacion del antecedente (Modus Tollens)
					for xj,u in enumerate(formulas[:]):
						if i!=xj and self.arbol[u['ind']]['op']=='neg' and self.iguales(self.arbol[u['ind']]['li'],self.arbol[v['ind']]['ld']):
						   	#aniadir al arbol un nuevo nodo con la negacion del antecedente
							if self.arbol.count({'op':'neg','tipo':None,'li':self.arbol[v['ind']]['li'], 'ld':None})==0:
								self.arbol.append({'op':'neg','tipo':None,'li':self.arbol[v['ind']]['li'], 'ld':None})
								ind=len(self.arbol)-1
								formulas.append({'ind':ind,'regla':'MT','oper':((i+1),(xj+1))})
								print "(%d) " % c,self.mostrarFBC(ind),"MT (%d) (%d)\n" % ((i+1),(xj+1))
								c+=1
								final=False
								break
					#ver si existe otra implicacion cuyo antecedente sea el consecuente de este 
					#para asi deducir una nueva implicacion con el antecedente de este y el consecuente de aquel (Silogismo)
					for xj,u in enumerate(formulas[:]):
						if i!=xj and self.arbol[u['ind']]['op']=='impl' and self.iguales(self.arbol[u['ind']]['li'],self.arbol[v['ind']]['ld']):
						   	#aniadir al arbol un nuevo nodo con una implicacion entre el antecedente del primero y el
						   	#consecuente del segundo
							if self.arbol.count({'op':'impl','tipo':'->','li':self.arbol[v['ind']]['li'],'ld':self.arbol[u['ind']]['ld']})==0:
								self.arbol.append({'op':'impl','tipo':'->','li':self.arbol[v['ind']]['li'],'ld':self.arbol[u['ind']]['ld']})
								ind=len(self.arbol)-1
								formulas.append({'ind':ind,'regla':'Sil','oper':((i+1),(xj+1))})
								print "(%d) " % c,self.mostrarFBC(ind),"Sil (%d) (%d)\n" % ((i+1),(xj+1))
								c+=1
								final=False
								break
					
				# regla de eliminacion de la doble negacion: negar doblemente algo es lo mismo que afirmarlo
				elif self.arbol[v['ind']]['op']=='neg' and self.arbol[self.arbol[v['ind']]['li']]['op']=='neg':
					if self.arbol[self.arbol[self.arbol[v['ind']]['li']]['li']]['op']=='agrup':
						ind=self.arbol[self.arbol[self.arbol[v['ind']]['li']]['li']]['li']
					else:
						ind=self.arbol[self.arbol[v['ind']]['li']]['li']
					if formulas.count({'ind':ind,'regla':'RE~~','oper':((i+1),)})==0:
						formulas.append({'ind':ind,'regla':'RE~~','oper':((i+1),)})
						print "(%d) " % c,self.mostrarFBC(ind),"RE~~ (%d)\n" % (i+1)
						c+=1
						final=False
				# regla de eliminacion de la coimplicacion
				elif self.arbol[v['ind']]['op']=='coimpl':
					if self.arbol.count({'op':'impl','tipo':'->','li':self.arbol[v['ind']]['li'],'ld':self.arbol[v['ind']]['ld']})==0:
						vli = self.arbol[v['ind']]['li']
						vld = self.arbol[v['ind']]['ld']
						self.arbol.append({'op':'impl','tipo':'->','li':vli,'ld':vld})
						ind = len(self.arbol)-1
						formulas.append({'ind':ind,'regla':'RE<->','oper':((i+1),)})
						print "(%d) " % c,self.mostrarFBC(ind),"RE<-> (%d)\n" % (i+1)
						self.arbol.append({'op':'impl','tipo':'->','li':vld,'ld':vli})
						ind = len(self.arbol)-1
						formulas.append({'ind':ind,'regla':'RE<->','oper':((i+1),)})
						print "(%d) " % (c+1),self.mostrarFBC(ind),"RE<-> (%d)\n" % (i+1)
						c+=2
						final=False
				# regla de eliminacion de la disyuncion
				elif (self.arbol[v['ind']]['op']=='conj_dis' and
				      self.arbol[v['ind']]['tipo']=='v'):
					if self.arbol[self.arbol[v['ind']]['li']]['op']=='agrup':
						ind=self.arbol[self.arbol[v['ind']]['li']]['li']
					else:
						ind=self.arbol[v['ind']]['li']
					if formulas.count({'ind':ind,'regla':'PAUX','oper':((i+1),)})==0:
				   		# suponemos verdadero cada uno de los componentes con caracter provisional
				   		# analizamos por separado ambos componentes y si obtenemos un mismo resultado concluimos este se
				   		# obtiene de la disyuncion y cancelamos los supuestos
				   		formulas.append({'ind':ind,'regla':'PAUX','oper':((i+1),)})
				   		print "(%d) " % c,self.mostrarFBC(ind),"P.A. \n" 
						c+=1
						final=False
						hay_disyuncion=set([len(formulas)])
						if self.arbol[self.arbol[v['ind']]['ld']]['op']=='agrup':
							ind=self.arbol[self.arbol[v['ind']]['ld']]['li']
						else:
							ind=self.arbol[v['ind']]['ld']
						formulas.append({'ind':ind,'regla':'PAUX','oper':((i+1),)})
				   		print "(%d) " % c,self.mostrarFBC(ind),"P.A. \n" 
						c+=1
						hay_disyuncion=hay_disyuncion|set([len(formulas)])
				# regla de introduccion de la conjuncion
				elif v['regla']!='Premisa' and i<nformulas-1:
					for j in range(i+1,nformulas):
						if self.arbol.count({'op':'conj_dis','tipo':'^','li':v['ind'],'ld':formulas[j]['ind']})==0:
							# si en una demostracion es verdad primero una formula y luego otra puede deducirse la conjuncion de ambas
							self.arbol.append({'op':'conj_dis','tipo':'^','li':v['ind'],'ld':formulas[j]['ind']})
							formulas.append({'ind':len(self.arbol)-1,'regla':'RI^','oper':((i+1),(j+1))})
							print "(%d) " % c,self.mostrarFBC(len(self.arbol)-1),"RI^ (%d) (%d)\n" % ((i+1),(j+1))
							c+=1
							final=False
							break
			if hay_disyuncion:
				# para cada nueva formula obtenida, ver si hay otra igual y que cada cual haya derivado de una de las
				# formulas (provisionales) de la disyuncion
				j=-1 #hay otra igual?
				for xj,u in enumerate(formulas[:-1]):
					if (formulas[-1]['ind']==u['ind'] or self.iguales(u['ind'],formulas[-1]['ind'])):
						j=xj
						break
				if j>=0:
					oper=[]
					# la ultima formula y la otra formula (igual a la ultima) derivan cada una de una PAUX?
					for i in (len(formulas)-1,j):
						k=formulas[i]['oper']
						cola=[]
						cola.append(k[0])
						camino=str(k[0])
						if len(k)==2:
							cola.append(k[1])
							camino+=','+str(k[1])
						# ir encolando los indices de las formulas de las cuales han derivado
						while True:
							if not cola:
								k=None
								break
							k=cola.pop(0)
							# alguno de dichos indices es una clausula auxiliar?
							if k in hay_disyuncion:
								break
							k=formulas[k-1]['oper']
							if k==None:
								continue
							cola.append(k[0])
							camino+=','+str(k[0])
							if len(k)==2:
								cola.append(k[1])
								camino+=','+str(k[1])
						if k:
							hay_disyuncion=hay_disyuncion-set([k])
							oper.append(camino)
					if len(hay_disyuncion)==0:		
						# anadir la ultima formula como valida, cancelando los supuestos
						hay_disyuncion=None
						formulas.append({'ind':formulas[-1]['ind'],'regla':'REv','oper':set(oper)})
				   		print "(%d) " % c,self.mostrarFBC(formulas[-1]['ind']),"REv ",["(%s)" % s for s in formulas[-1]['oper']] 
						c+=1		
						final=False	
			# se ha alcanzado la conclusion?
			if not hay_disyuncion:
				for j in reversed(xrange(nformulas,len(formulas))):
					if self.iguales(self.premisas[-1],formulas[j]['ind']):
						final=True	
						break	
			if reduccionAbsurdo and self.contradiccion(formulas[-1]['ind']):
				# se ha obtenido una formula cuya tabla de Verdad tiene todas las entradas a False
				for j,u in enumerate(formulas[:]):
					if u['regla']=='PA':
						break
				# hay que negar la formula que ha dado lugar a la contradiccion
				self.arbol.append({'op':'neg','tipo':None,'li':u['ind'],'ld':None})
				formulas.append({'ind':len(self.arbol)-1,'regla':'RI~','oper':((j+1),)})
				print "(%d) " % c,self.mostrarFBC(len(self.arbol)-1),"RI~ (%d) \n" % (j+1)
				final=False
				c+=1
			if final:
				break
						
	def ProcesarError(self,TipoError):
		if(TipoError == 1):
			print "Error: no se parea"
		elif(TipoError == 2):
			print "Error: entrada en la tabla erronea"
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
	def ParserDescendente(self): #el buffer de entrada,formada solo por terminales, contiene la cadena que se va a analizar				
		self.CrearTablaAnSin()
		Pila = ['$']  # la pila almacena el trabajo que falta por hacer, en forma de variables que se tienen aun que emparejar
		Pila.append(self.S)
		a,l = self.LeerSigTerm()
		X = Pila.pop()
		while not (X==a and X=='$'):
			if X in self.acciones_sem:
				if X=='introd_conec':
					self.introd_conec()
				elif X=='introd_prop':
					self.introd_prop(vl)
				elif X=='introd_neg':
					self.introd_neg()
				elif X=='agrupar':
					self.agrupar()
				elif X=='nueva_premisa':
					self.nueva_premisa()
				elif X=='guardar':
					self.guardar(va,vl)
				elif X=='obtenerTablaVerdad':
					self.obtenerTablaVerdad()
				elif X=='demostrarArgumento':
					if len(sys.argv)>2 and sys.argv[2]=='True':
						self.demostrarArgumento(True)
					else:
						self.demostrarArgumento(False)
				X=Pila.pop()
				continue
			if X==a and a!='$':
				va,vl = a,l
				a,l = self.LeerSigTerm()
			elif X!=a:
				if X in self.T:
					self.ProcesarError(1)
				else:
					if len(self.M[X][a])==0:
						self.ProcesarError(2)
					else:
						if not self.M[X][a][0]=='lambda':
							for I in reversed(self.M[X][a]):
								Pila.append(I)
			X = Pila.pop()
				

#reglas = {'E':[['T','EP']],'EP':[['+','T', 'EP'],['lambda']],'T':[['F','TP']],'TP':[['*','F','TP'],['lambda']],'F':[['n'],['(','E',')']]}				
#gramaticaExpr = G(['*','+','n','(',')'],['E','T','EP','F','TP'],'E',reglas)
#gramaticaExpr.CalcularPrimero()
#gramaticaExpr.MostrarPrimero()
#gramaticaExpr.CalcularSiguiente()
#gramaticaExpr.MostrarSiguiente()
#gramaticaExpr.CrearTablaAnSin()
#gramaticaExpr.MostrarTablaAnSin()
#gramaticaExpr.ParserDescendente()                  
						
Glflp = G()
Glflp.ParserDescendente()
#Glflp.displayarTablaAnSin()

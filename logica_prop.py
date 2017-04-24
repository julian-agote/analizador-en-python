#!/usr/bin/env python
import sys
def concatenar(s1,s2):
	return s1+' '+s2
def hacer_lista(s1,s2):
	return s1+"\',\'"+s2	
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
		#self.f = open(sys.argv[1],'r')
		self.acciones_sem = ['introd_conec','introd_neg','introd_prop','agrupar','nueva_premisa',
					   'guardar','obtenerTablaVerdad','demostrarArgumento']
		self.pila_sem =[]
		self.arbol=[]
		self.premisas=[]
		self.posicion={} # para saber a cada prop. que posicion le corresponde en el array de V,F
		self.posicion_aux={}
		self.estado=[]   # para ir guardando los sucesivos valores de verdad de las proposiciones
		self.colec_lr0=[]
		self.tir_a=[]
		self.siguiente_marca = 0
		self.taccion=[]
	def nuevo_marcador(self,preglas,pacc,inicio):
		for k,v in preglas.iteritems():
			for x in v:
				alfa,acc=x
				if acc==pacc:
					return k
		if not inicio:
			for k,v in self.P.iteritems():
				for x in v:
					alfa,acc=x
					if acc==pacc:
						return k			
		self.siguiente_marca+=1
		return "M%s" %(self.siguiente_marca)
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
	def calcularPrimeroAsc(self):
		for I in self.T:
			self.Primero[I] = [I]
		for X in self.V:
			for v in self.P[X]:
				r,acc=v
				if r[0]=='lambda':
					self.Primero[X] = ['lambda']
		Final = False
		while not Final:
			Final = True
			for X in self.V:
				for v in self.P[X]:
					alfa,acc=v
					cadena = alfa
					YaEsta = False
					while not YaEsta and len(cadena)>0:
						Y = cadena[0]
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
			for i,v in enumerate(formulas[:]):
				nformulas=len(formulas)
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
						# ver si se obtuvo una formula igual
						ya_esta = False
						for f in formulas:
							if(f['ind']==ind or self.iguales(f['ind'],ind)):
								ya_esta=True
						if not ya_esta or hay_disyuncion:		
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
						# ver si se obtuvo una formula igual
						ya_esta = False
						for f in formulas:
							if(f['ind']==ind or self.iguales(f['ind'],ind)):
								ya_esta=True
						if not ya_esta or hay_disyuncion:		
							formulas.append({'ind':ind,'regla':'RE^','oper':((i+1),)})
							print "(%d) " % (c+1),self.mostrarFBC(ind),"RE^ (%d)\n" % (i+1)
							c+=2					
				# leyes de morgan
				elif self.arbol[v['ind']]['op']=='neg' and self.arbol[self.arbol[v['ind']]['li']]['op']=='agrup':
					ind=self.arbol[self.arbol[v['ind']]['li']]['li']
					if self.arbol[ind]['op']=='conj_dis':
						if self.arbol[ind]['tipo']=='^':
							v_tipo='v'
						else:
							v_tipo='^'
						self.arbol.append({'op':'neg','tipo':None,'li':self.arbol[ind]['li'], 'ld':None})
						self.arbol.append({'op':'neg','tipo':None,'li':self.arbol[ind]['ld'], 'ld':None})
						self.arbol.append({'op':'conj_dis','tipo':v_tipo,'li':len(self.arbol)-2, 'ld':len(self.arbol)-1})	
						formulas.append({'ind':len(self.arbol)-1,'regla':'LM','oper':((i+1),)})
						print "(%d) " % c,self.mostrarFBC(len(self.arbol)-1),"LM (%d)\n" % (i+1)
						c+=1
						final=False						

				# regla de eliminacion de la implicacion 
				elif self.arbol[v['ind']]['op']=='impl':
					# ver si existe una formula que coincide con self.arbol[v['ind']]['li'] (modus ponens)
					vj=[]
					for xj,u in enumerate(formulas[:]):
						if i!=xj and (self.arbol[v['ind']]['li']==u['ind'] or self.iguales(u['ind'],self.arbol[v['ind']]['li'])):
							vj.append(xj)
					for j in vj:
						if self.arbol[self.arbol[v['ind']]['ld']]['op']=='agrup':
							ind=self.arbol[self.arbol[v['ind']]['ld']]['li']
						else:
							ind=self.arbol[v['ind']]['ld']
						if formulas.count({'ind':ind,'regla':'RE->','oper':((i+1),(j+1))})==0:
							# ver si se obtuvo una formula igual
							ya_esta = False
							for f in formulas:
								if(f['ind']==ind or self.iguales(f['ind'],ind)):
									ya_esta=True
							if not ya_esta or hay_disyuncion:		
								# si una implicacion es verdadera y tambien lo es su antecedente podemos deducir su consecuente
								formulas.append({'ind':ind,'regla':'RE->','oper':((i+1),(j+1))})
								print "(%d) " % c,self.mostrarFBC(ind),"RE-> (%d) (%d)\n" % ((i+1),(j+1))
								c+=1
								final=False
								if not hay_disyuncion:
									break
					#ver si existe una formula con la negacion del consecuente, para asi deducir
					# la negacion del antecedente (Modus Tollens)
					for xj,u in enumerate(formulas[:]):
						if i!=xj and ((self.arbol[u['ind']]['op']=='neg' and self.iguales(self.arbol[u['ind']]['li'],self.arbol[v['ind']]['ld'])) or
						                 (self.arbol[self.arbol[v['ind']]['ld']]['op']=='neg' and self.iguales(u['ind'],self.arbol[self.arbol[v['ind']]['ld']]['li']))):
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
						# ver si se obtuvo una formula igual
						ya_esta = False
						for f in formulas:
							if(f['ind']==ind or self.iguales(f['ind'],ind)):
								ya_esta=True
						if not ya_esta or hay_disyuncion:		
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
						if self.iguales(self.premisas[-1],formulas[-1]['ind']):
							final=True
							break
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
						# ver si se obtuvo una formula igual
						ya_esta = False
						for xi,f in enumerate(formulas):
							if(f['ind']==ind or self.iguales(f['ind'],ind)):
								hay_disyuncion=set([xi])
								ya_esta=True
						if not ya_esta:		
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
						# ver si se obtuvo una formula igual
						ya_esta = False
						for xi,f in enumerate(formulas):
							if(f['ind']==ind or self.iguales(f['ind'],ind)):
								hay_disyuncion=hay_disyuncion|set([xi])
								ya_esta=True
						if not ya_esta:
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
				# ver si se obtiene la conclusion
				if self.iguales(self.premisas[-1],formulas[-1]['ind']):
					final=True
					if reduccionAbsurdo:
						# anadir una nueva formula formada por la conjuncion de la conclusion (deducida) y la negacion de la conclusion utiliza como premisa auxiliar
						self.arbol.append({'op':'neg','tipo':None,'li':self.premisas[-1], 'ld':None})
						self.arbol.append({'op':'conj_dis','tipo':'^','li':formulas[-1]['ind'],'ld':len(self.arbol)-1})
						formulas.append({'ind':len(self.arbol)-1,'regla':'RI^','oper':(len(formulas),len(premisas))})
						print "(%d) " % c,self.mostrarFBC(len(self.arbol)-1),"RI^ (%d) (%d)\n" % (len(formulas),len(premisas))
						c+=1
						
					break

			if hay_disyuncion:
				# para cada nueva formula obtenida, ver si hay otra igual y que cada cual haya derivado de una de las
				# formulas (provisionales "premisas auxiliares") de la disyuncion
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
			else:
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
				final=True
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
	def cerradura(self,conj):
		while True:
			final = True
			aux_conj = {}
			for k,v in conj.iteritems():
				for x in v:
					beta,s=x
					for i in range(len(beta)):
						if i<len(beta)-1 and beta[i]=="." and beta[i+1] in self.V:
							if beta[i+1] in conj.keys():
								enc=False
								for r in conj[beta[i+1]]:
									z,y = r
									if z[0]==".":
										enc=True
										break
								if not enc:
									simbant = self.CalcularPrimeroCad(beta[i+2:])
									if "lambda" in simbant:
										del simbant[simbant.index("lambda")]
										simbant += s
									for pdcha in self.P[beta[i+1]]:
										alfa,acc = pdcha
										if beta[i+1] in aux_conj.keys():
											aux_conj[beta[i+1]].append((["."]+alfa,simbant))
										else:
											aux_conj[beta[i+1]]=[(["."]+alfa,simbant)]
										final = False
							else:
								simbant = self.CalcularPrimeroCad(beta[i+2:])
								if "lambda" in simbant:
									del simbant[simbant.index("lambda")]
									simbant += s
								for pdcha in self.P[beta[i+1]]:
									alfa,acc=pdcha
									if beta[i+1] in aux_conj.keys():
										aux_conj[beta[i+1]].append((["."]+alfa,simbant))
									else:
										aux_conj[beta[i+1]]=[(["."]+alfa,simbant)]
									final = False							
			if final:
				break
			else:
				for k,v in aux_conj.iteritems():
					if k in conj.keys():
						for r in aux_conj[k]:
							conj[k].append(r)
					else:
						conj[k]=v
	def mostrar_cjto(self,conj):
		for k,v in conj.iteritems():
			for x in v:
				beta,s=x
				print k,'->',reduce(concatenar,beta),',',reduce(concatenar,s)
	def ir_a(self,conj,X):
		nconj={} #dict([(I,[]) for I in self.V+[self.S+"prima"]])
		for k,v in conj.iteritems():
			for y in v:
				beta,s=y
				for j in range(len(beta)):
					if j<len(beta)-1 and beta[j]=="." and beta[j+1]==X:
						if k in nconj.keys():
							nconj[k].append((beta[0:j]+[beta[j+1],"."]+beta[j+2:],s))
						else:
							nconj[k]=[(beta[0:j]+[beta[j+1],"."]+beta[j+2:],s)]
		if nconj:
			self.cerradura(nconj)
		return nconj
	def igual(self,nconj,pconj,i):
		if set(nconj.keys())!=set(pconj.keys()):
			return False
		for k,v in nconj.iteritems():
			if len(v)!=len(pconj[k]):
				return False
			for y in v:
				beta,s=y
				existe=False
				for j in pconj[k]:
					alfa,s2=j
					if beta==alfa and set(s)==set(s2):
						existe=True
						break
				if not existe:
					return False
		return True
	def	calcular_colec_lr1(self):
		conj={} #dict([(I,[]) for I in self.V])
		conj[self.S+"prima"]=[([".",self.S],["$"])]
		self.cerradura(conj)
		self.colec_lr0.append(conj)
		sig=ult=0
		while sig<=ult:
			fila_ira={}
			for X in self.T+self.V:
				conj=self.ir_a(self.colec_lr0[sig],X)
				if conj:
					sig_estado = ult + 1
					for k in range(len(self.colec_lr0)):
						if self.igual(conj,self.colec_lr0[k],k):
							sig_estado = k
							break
					if sig_estado == (ult + 1):
						self.colec_lr0.append(conj)
						ult +=1
					fila_ira[X]=sig_estado
			self.tir_a.append(fila_ira)
			sig+=1
	def mostrar_elementos(self):
		for i in range(len(self.colec_lr0)):
			print "I%s:" %(i)
			self.mostrar_cjto(self.colec_lr0[i])
	def aumentar_gramatica(self):
		self.P[self.S+"prima"]=[[self.S]]
		self.V.append(self.S+"prima")
		aux_reglas={}
		for k,v in self.P.iteritems():
			for alfa in v:
				enc_acc=False
				for i in range(len(alfa)):
					if alfa[i] in self.acciones_sem:
						enc_acc=True
						if i<len(alfa)-1:
							m=self.nuevo_marcador(aux_reglas,alfa[i],True)
							if m not in self.V:
								self.V.append(m)
								aux_reglas[m]=[(['lambda'],alfa[i])]
							del alfa[i]
							alfa.insert(i,m)
							if k in aux_reglas.keys():
								aux_reglas[k].append((alfa,""))
							else:
								aux_reglas[k]=[(alfa,"")]
						else:
							acc=alfa[i]
							del alfa[i]
							if k in aux_reglas.keys():
								aux_reglas[k].append((alfa,acc))
							else:
								aux_reglas[k]=[(alfa,acc)]
						break
				if not enc_acc:
					if k in aux_reglas.keys():
						aux_reglas[k].append((alfa,""))
					else:
						aux_reglas[k]=[(alfa,"")]
		self.P={}
		for k,v in aux_reglas.iteritems():		
			self.P[k]=v
		while True:
			final = True
			aux_reglas={}
			for k,v in self.P.iteritems():
				for x in v:
					alfa,acc_sem=x
					enc_acc=False
					for i in range(len(alfa)):
						if alfa[i] in self.acciones_sem:
							enc_acc=True
							if i<len(alfa)-1:
								m=self.nuevo_marcador(aux_reglas,alfa[i],False)
								if m not in self.V:
									self.V.append(m)
									aux_reglas[m]=[(['lambda'],alfa[i])]
								del alfa[i]
								alfa.insert(i,m)
								if k in aux_reglas.keys():
									aux_reglas[k].append((alfa,acc_sem))
								else:
									aux_reglas[k]=[(alfa,acc_sem)]
							else:
								acc=alfa[i]
								del alfa[i]
								if k in aux_reglas.keys():
									aux_reglas[k].append((alfa,acc))
								else:
									aux_reglas[k]=[(alfa,acc)]
							break
					if not enc_acc:
						if k in aux_reglas.keys():
							aux_reglas[k].append((alfa,acc_sem))
						else:
							aux_reglas[k]=[(alfa,acc_sem)]
					else:
						final = False
			self.P={}
			for k,v in aux_reglas.iteritems():		
				self.P[k]=v
			if final:
				break
		#eliminar marcadores al final
		aux_reglas={}
		for k,v in self.P.iteritems():
			for x in v:
				alfa,acc_sem=x
				#ver si alfa[len(alfa)-1] es uno de los marcadores
				if alfa[-1] in self.V and len(self.P[alfa[-1]])==1:
					beta,acc=self.P[alfa[-1]][0]
					if beta==['lambda']:
						del alfa[-1]
						if k in aux_reglas.keys():
							aux_reglas[k].append((alfa,acc+";"+acc_sem))
						else:
							aux_reglas[k]=[(alfa,acc+";"+acc_sem)]
					else:
						if k in aux_reglas.keys():
							aux_reglas[k].append((alfa,acc_sem))
						else:
							aux_reglas[k]=[(alfa,acc_sem)]
				else:
					if k in aux_reglas.keys():
						aux_reglas[k].append((alfa,acc_sem))
					else:
						aux_reglas[k]=[(alfa,acc_sem)]
		self.P={}
		for k,v in aux_reglas.iteritems():		
			self.P[k]=v
		self.eliminarSimbolosNoAccesibles()
	def eliminarSimbolosNoAccesibles(self):
		vaccesibles=[self.S+"prima"]
		taccesibles=[]
		while True:
			vaux=taux=[]
			for k,v in self.P.iteritems():
				if k in vaccesibles:
					for x in v:
						alfa,acc_sem=x
						if alfa!=['lambda']:
							for s in alfa:
								if s in self.V and s not in vaccesibles and s not in vaux:
									vaux.append(s)
								elif s in self.T and s not in taccesibles and s not in taux:
									taux.append(s)
			if len(vaux)==0 and len(taux)==0:
				break
			vaccesibles.extend(vaux)
			taccesibles.extend(taux)
		#eliminar las reglas de produccion que tengan simbolos no accesibles en su parte izda o dcha.
		paux={}
		for k,v in self.P.iteritems():
			if k in vaccesibles:
				for x in v:
					alfa,acc_sem=x
					todos_accesibles=True
					for s in alfa:
						if s not in vaccesibles and s not in taccesibles:
							todos_accesibles = False
							break
					if k in paux.keys():
						paux[k].append(x)
					else:
						paux[k]=[x]
		self.P={}
		for k,v in paux.iteritems():		
			self.P[k]=v
	def calcular_tabla_accion(self):
		for i in range(len(self.colec_lr0)):
			accion={}
			for k,v in self.colec_lr0[i].iteritems():
				for x in v:
					alfa,s=x
					pos_punto=alfa.index(".")
					if pos_punto<len(alfa)-1 and alfa[pos_punto+1] in self.T:
						if alfa[pos_punto+1] in accion.keys():
							print "La gramatica no es LR(1), conflicto en estado ",i," con simbolo ",alfa[pos_punto+1]," accion desplazar "
							return False
						elif alfa[pos_punto+1] in self.tir_a[i].keys():
							accion[alfa[pos_punto+1]]=("desplazar",self.tir_a[i][alfa[pos_punto+1]])
						else:
							print "No hay estado siguiente, desde estado ",i," con simbolo ",alfa[pos_punto+1]
							return False
			for k,v in self.colec_lr0[i].iteritems():
				for x in v:
					alfa,s=x
					pos_punto=alfa.index(".")
					if pos_punto==len(alfa)-1 or alfa[pos_punto+1]=='lambda':
						if k==self.S+"prima" and s.count("$")>0:
							op="aceptar"
						else:
							op="reducir"
						for y in s:
							if y in accion.keys():
								print "La gramatica no es LR(1), conflicto en estado ",i," con simbolo ",y," accion reducir "
								return False
							else:
								regla={}
								if pos_punto==len(alfa)-1:
									regla[k]=alfa[:-1]
								else:
									regla[k]=['lambda']
								accion[y]=(op,regla)
			self.taccion.append(accion)
		return True
	def escribe_compilador(self):
		f1=open("par_logica.py","w")
		f1.write("#!/usr/bin/env python\n")
		f1.write("import sys\n")
		f1.write("class G:\n")
		f1.write("\tdef __init__(self):\n")
		f1.write("\t\tself.P={")
		for k,v in self.P.iteritems():
			f1.write("\'"+k+"\':[")
			for x in v:
				alfa,acc=x
				f1.write("([\'"+reduce(hacer_lista,alfa)+"\'],\'"+acc+"\'),")
			f1.write("],\n\t\t\t")
		f1.write("}\n")	
		f1.write("\t\tself.taccion=[")
		for x in self.taccion:
			f1.write("{")
			for k,v in x.iteritems():
				f1.write("\'"+k+"\':")
				op,s=v
				f1.write("(\'"+op+"\',")
				if op=="desplazar":
					f1.write(str(s)+")")
				else:
					for clave,valor in s.iteritems():
						f1.write("{\'"+clave+"\':[")
						for i,z in enumerate(valor):
							if i==len(valor)-1:
								f1.write("\'"+z+"\']})")
							else:
								f1.write("\'"+z+"\',")
				f1.write(",")
			f1.write("},\n             \t\t")
		f1.write("]\n")
		f1.write("\t\tself.tir_a=[")
		for x in self.tir_a:
			f1.write("{")
			for k,v in x.iteritems():
				f1.write("\'"+k+"\':"+str(v)+",")
			f1.write("},\n            \t\t")
		f1.write("]\n")
		f1.write("\t\tself.f = open(sys.argv[1],\'r\')\n")
		f1.write("\tdef parserAscendente(self):\n")
		f1.write("\t\tpila=[0]\n")
		f1.write("\t\ta,l = self.LeerSigTerm()\n")
		f1.write("\t\twhile True:\n")
		f1.write("\t\t\testado=pila[-1]\n")
		f1.write("\t\t\tif not a in self.taccion[estado].keys():\n")
		f1.write("\t\t\t\tprint \'Error, falta entrada en accion, estado \',estado,\' con \',a\n")
		f1.write("\t\t\t\treturn False\n")
		f1.write("\t\t\telse:\n")
		f1.write("\t\t\t\top,r=self.taccion[estado][a]\n")
		f1.write("\t\t\t\tif op==\'reducir\':\n")
		f1.write("\t\t\t\t\t#sacar tantos elementos de la pila como simbolos hay en la parte dcha. de la regla de reduccion\n")
		f1.write("\t\t\t\t\tk=r.keys()\n")
		f1.write("\t\t\t\t\tif r[k[0]]!=[\'lambda\']:\n")
		f1.write("\t\t\t\t\t\tfor i in range(len(r[k[0]])):\n")
		f1.write("\t\t\t\t\t\t\tpila.pop()\n")
		f1.write("\t\t\t\t\t#meter en la pila el estado que corresponde a introducir la vble de la parte izda. de la regla\n")
		f1.write("\t\t\t\t\tif k[0] not in self.tir_a[pila[-1]]:\n")
		f1.write("\t\t\t\t\t\tprint \'Error:falta el estado al cual ir despues de reducir \',pila[-1],\' con \',k[0]\n")
		f1.write("\t\t\t\t\t\treturn False\n")
		f1.write("\t\t\t\t\tpila.append(self.tir_a[pila[-1]][k[0]])\n")
		f1.write("\t\t\t\t\t#ejecutar la accion semantica correspondiente a la regla reducida\n")
		f1.write("\t\t\t\t\tfor n,v in self.P.iteritems():\n")
		f1.write("\t\t\t\t\t\tif n==k[0]:\n")
		f1.write("\t\t\t\t\t\t\tfor x in v:\n")
		f1.write("\t\t\t\t\t\t\t\tp,acc_sem=x\n")
		f1.write("\t\t\t\t\t\t\t\tif r[k[0]]==p and acc_sem:\n")
		f1.write("\t\t\t\t\t\t\t\t\tprint \'Ejecutar \',acc_sem\n")
		f1.write("\t\t\t\telif op==\'desplazar\':\n")
		f1.write("\t\t\t\t\tpila.append(r)\n")
		f1.write("\t\t\t\t\ta,l = self.LeerSigTerm()\n")
		f1.write("\t\t\t\telif op==\'aceptar\' and a==\'$\':\n")
		f1.write("\t\t\t\t\treturn True\n")
		f1.write("\t\t\t\telse:\n")
		f1.write("\t\t\t\t\tprint \'Error: la entrada continua y se ha llegado a un estado de aceptacion\'\n")
		f1.write("\t\t\t\t\treturn False\n")
		f1.write("Glflp = G()\n")
		f1.write("Glflp.parserAscendente()\n")
		f1.close()
	def mostrar_situacion(self,pila,accion,leido):
		cad=""
		for x in pila:
			cad+= str(x)+" "
		cad+= accion+" "
		for y in leido:
			cad+= y+" "
		print cad
	def parserAscendente(self):
		leido=[]
		pila=[0]
		a,l = self.LeerSigTerm()
		leido.append(l)
		while True:
			estado=pila[-1]
			if not a in self.taccion[estado].keys():
				print "Error, falta entrada en accion, estado ",estado," con ",a
				return False
			else:
				op,r=self.taccion[estado][a]
				if op=="reducir":
					#sacar tantos elementos de la pila como simbolos hay en la parte dcha. de la regla de reduccion
					k=r.keys()
					if r[k[0]]!=["lambda"]:
						for i in range(len(r[k[0]])):
							pila.pop()
					#meter en la pila el estado que corresponde a introducir la vble de la parte izda. de la regla
					if k[0] not in self.tir_a[pila[-1]]:
						print "Error:falta el estado al cual ir despues de reducir ",pila[-1]," con ",k[0]
						return False
					pila.append(self.tir_a[pila[-1]][k[0]])
					#ejecutar la accion semantica correspondiente a la regla reducida
					for n,v in self.P.iteritems():
						if n==k[0]:
							for x in v:
								p,acc_sem=x
								if r[k[0]]==p and acc_sem:								
									print "Ejecutar ",acc_sem
					self.mostrar_situacion(pila,"r por "+k[0]+"->"+reduce(concatenar,r[k[0]]),leido)
				elif op=="desplazar":
					pila.append(r)
					a,l = self.LeerSigTerm()
					leido.append(l)
					self.mostrar_situacion(pila,"d"+str(r),leido)
				elif op=="aceptar" and a=='$':
					return True
				else:
					print "Error: la entrada continua y se ha llegado a un estado de aceptacion"
					return False
	def mostrar_reglas(self):
		for k,v in self.P.iteritems():
			for x in v:
				alfa,acc=x
				cad = k+"->"
				for i in range(len(alfa)):
					if i<len(alfa)-1:
						cad+=alfa[i]+" "
					else:
						cad+=alfa[i]+","
				cad+=acc
				print cad
				
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
Glflp.aumentar_gramatica()
Glflp.mostrar_reglas()
Glflp.calcularPrimeroAsc()
Glflp.calcular_colec_lr1()
#Glflp.mostrar_elementos()
if Glflp.calcular_tabla_accion():
	Glflp.escribe_compilador()
	#Glflp.parserAscendente()


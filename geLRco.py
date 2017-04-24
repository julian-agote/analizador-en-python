#!/usr/bin/env python
import sys,string
def concatenar(s1,s2):
	return s1+' '+s2
def hacer_lista(s1,s2):
	return s1+"\',\'"+s2	
class G:
	def __init__(self):
		self.T = ['letra','digito','[',']','(',')','{','}','flecha','coma','+','*','?','-','^','punto','&','%%TERMS','%%NO_TERMS','%%DECLS',
		          '%%AXIOMA','%%REGLAS','%%ACCIONES_SEMANTICAS','barra','_',';','comilla_simple','comilla_doble','simbolo','cod']
		self.V = ['S','partedeclarativa','partedeclarativap','reglas','id','er','erp','ercierre','eru','tipocierre','eralter','rango','rangop','compl','letras','pcod',
		          'letrasp','idp','pdcha','listaid','listaidp','declaraciones','terminales','variables','axioma','acciones','producciones',
				  'listatoken','listatokenp','defEr','defDecl','caracteres','simbolos','simbolosp','digitos','digitosp']
		self.S = 'S'
		self.P = {'S':['declaraciones terminales variables axioma acciones producciones'.split()],
				  'declaraciones':[['%%DECLS','partedeclarativa'],['lambda']],
				  'terminales':[['%%TERMS','inicio_escaner','listatoken','fin_escaner'],['lambda']],
				  'variables':[['%%NO_TERMS','vaciar_pila','listaid','poner_vbles'],['lambda']],
				  'axioma':[['%%AXIOMA','id','poner_axioma'],['lambda']],
				  'acciones':[['%%ACCIONES_SEMANTICAS','listaid','poner_acciones'],['lambda']],
				  'producciones':[['%%REGLAS','reglas','escribe_parser'],['lambda']],
	              'partedeclarativa':['id er poner_declaracion pcod partedeclarativap'.split()],
				  'partedeclarativap':['id er poner_declaracion pcod partedeclarativap'.split(),['lambda']],
	              'er':['ercierre erp'.split()],
				  'erp':['ercierre concatenacion erp'.split(),['lambda']],
	              'ercierre':['eru tipocierre'.split()],
	              'tipocierre':[['+','poner_cierre_positivo'],['*','poner_cierre'],['?'],['lambda']],
	              'eru':['( er eralter )'.split(),['defDecl'],'[ compl rango ]'.split()],
	              'eralter':['barra er poner_alternativa eralter'.split(),['lambda']],
	              'rango':['letra guarda - letra guarda poner_rango_guion rangop'.split(),'digito guarda - digito guarda poner_rango_guion rangop'.split(),['defDecl rangop']],
				  'rangop':[['compl','rango'],['lambda']],
				  'compl':[['^'],['lambda']],
				  'pcod':[['cod'],['lambda']],
				  'defDecl':[['comilla_doble','caracteres','comilla_doble','poner_como_tupla'],['comilla_simple','caracteres','comilla_simple','poner_como_tupla'],['{','id','}','recuperar_decl_ant']],
				  'letras':[['letra','guarda','letrasp']],
				  'letrasp':[['letra','compone','letrasp'],['lambda']],
				  'digitos':[['digito','guarda','digitosp']],
				  'digitosp':[['digito','compone','digitosp'],['lambda']],
				  'id':[['letra','guarda','idp']],
				  'idp':[['letra','compone','idp'],['digito','compone','idp'],['_','compone','idp'],['lambda']],
				  'reglas':['id nueva_pizda flecha pdcha ; termina_regla reglas'.split(),['lambda']],
				  'pdcha':['& id nuevo_simbolo pdcha'.split(),'[ id nueva_accion ] pdcha'.split(),'barra nueva_pdcha pdcha'.split(),['lambda']],
				  'listaid':[['id','listaidp']],
				  'listaidp':[['coma','id','listaidp'],['lambda']],
				  'listatoken':['id defEr listatokenp'.split()],
				  'listatokenp':['id defEr listatokenp'.split(),['lambda']],
				  'defEr':[['comilla_doble','caracteres','comilla_doble','codigo_literal'],['comilla_simple','caracteres','comilla_simple','codigo_literal'],['{','id','}','codigo_declaracion']],
				  'caracteres':[['letras'],['simbolos'],['punto'],['digitos']],
				  'simbolos':[['simbolo','guarda','simbolosp'],['(','guarda','simbolosp'],[')','guarda','simbolosp'],['coma','guarda','simbolosp'],['-','guarda','simbolosp'],
				              ['{','guarda','simbolosp'],['}','guarda','simbolosp'],['[','guarda','simbolosp'],[']','guarda','simbolosp'],['_','guarda','simbolosp'],['^','guarda','simbolosp'],['%','guarda','simbolosp'],
							  ['+','guarda','simbolosp'],['*','guarda','simbolosp'],['?','guarda','simbolosp'],[';','guarda','simbolosp'],['&','guarda','simbolosp'],['barra','guarda','simbolosp'],['flecha','guarda','simbolosp']],
				  'simbolosp':[['simbolo','compone','simbolosp'],['(','compone','simbolosp'],[')','compone','simbolosp'],['coma','compone','simbolosp'],['-','compone','simbolosp'],
				               ['[','compone','simbolosp'],[']','compone','simbolosp'],['{','compone','simbolosp'],['}','compone','simbolosp'],['_','compone','simbolosp'],['^','compone','simbolosp'],['%','compone','simbolosp'],
                               ['+','compone','simbolosp'],['*','compone','simbolosp'],['?','compone','simbolosp'],[';','compone','simbolosp'],['&','compone','simbolosp'],['barra','compone','simbolosp'],['flecha','compone','simbolosp'],['lambda']]
				  }
		self.acciones_sem = ['nueva_pizda','nuevo_simbolo','nueva_pdcha','termina_regla','guarda','compone','vaciar_pila','poner_axioma','poner_vbles','poner_acciones',
		                     'inicio_escaner','codigo_literal','fin_escaner','poner_alternativa','poner_rango_guion','poner_declaracion','codigo_declaracion','poner_cierre_positivo',
							 'poner_cierre','concatenacion','recuperar_decl_ant','poner_como_tupla','escribe_parser','nueva_accion']
		self.Primero = {};
		self.Siguiente = {};
		self.M = {}  # es la tabla de analisis sintactico M[A,a] en la que se indica la regla a aplicar partiendo del
		             # no terminal A cuando el siguiente simbolo de la entrada es a
		self.f = open(sys.argv[1],'r')
		self.pila_sem =[]
		self.colec_lr0=[]
		self.tir_a=[]
		self.siguiente_marca = 0
		self.taccion=[]
		self.V2=[]
		self.T2=[]
		self.S2=''
		self.acciones_sem2 = []
		self.P2={}
		self.colec_lr0_2=[]
		self.tir_a2=[]
		self.taccion2=[]
		self.decls={}
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
	def calcularPrimeroAsc2(self):
		self.Primero={}
		for I in self.T2:
			self.Primero[I] = [I]
		for X in self.V2:
			for v in self.P2[X]:
				r,acc=v
				if r[0]=='lambda':
					self.Primero[X] = ['lambda']
		Final = False
		while not Final:
			Final = True
			for X in self.V2:
				for v in self.P2[X]:
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
		if CarSgte in ('(',')','[',']','{','}','_','^','+','*','?',';','&'):
			token = CarSgte
		elif CarSgte == '.':
			token = 'punto'
		elif CarSgte == '\"':
			token = 'comilla_doble'
		elif CarSgte == '\'':
			token = 'comilla_simple'
		elif CarSgte == '\\':
			token = 'simbolo'
			CarSgte = self.f.read(1)
			lexema+=CarSgte
		elif CarSgte == ',':
			token = 'coma'
		elif CarSgte == '|':
			token = 'barra'
		elif CarSgte =='-':
			CarSgte = self.f.read(1)
			if CarSgte =='>':
				lexema += CarSgte
				token = 'flecha' 	
			else:
				self.f.seek(-1, 1) #vuelve atras la posicion leida
				token = '-'
		elif CarSgte=='%': 
			CarSgte = self.f.read(1)
			if CarSgte=='%':
				lexema+=CarSgte
				CarSgte = self.f.read(1)
				while(CarSgte in [chr(i) for i in range(ord('A'),ord('Z')+1)]+['_']):
					lexema+=CarSgte
					CarSgte = self.f.read(1)
				if lexema=="%%TERMS":
					token="%%TERMS"
				elif lexema=="%%NO_TERMS":
					token="%%NO_TERMS"
				elif lexema=="%%DECLS":
					token="%%DECLS"
				elif lexema=="%%REGLAS":
					token="%%REGLAS"
				elif lexema=="%%AXIOMA":
					token="%%AXIOMA"
				elif lexema=="%%ACCIONES_SEMANTICAS":
					token="%%ACCIONES_SEMANTICAS"
			elif CarSgte=='{':
				CarSgte = self.f.read(1)
				lexema=CarSgte
				while(CarSgte != '%'):
					lexema+=CarSgte
					CarSgte = self.f.read(1)
				CarSgte = self.f.read(1)
				if CarSgte == '}':
					token = "cod"
			else:
				self.f.seek(-1, 1) #vuelve atras la posicion leida
				token = '%'
		elif CarSgte in [chr(i) for i in range(ord('a'),ord('z'))]+['z']+[chr(i) for i in range(ord('A'),ord('Z'))]+['Z']:
			token = 'letra'
		elif CarSgte in [chr(i) for i in range(ord('0'),ord('9')+1)]:
			token = 'digito'
		else:
			token = 'simbolo'	
		#print "lexema=",lexema
		return (token,lexema)
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
	def cerradura2(self,conj):
		while True:
			final = True
			aux_conj = {}
			for k,v in conj.iteritems():
				for x in v:
					beta,s=x
					for i in range(len(beta)):
						if i<len(beta)-1 and beta[i]=="." and beta[i+1] in self.V2:
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
									for pdcha in self.P2[beta[i+1]]:
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
								for pdcha in self.P2[beta[i+1]]:
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
	def ir_a2(self,conj,X):
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
			self.cerradura2(nconj)
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
	def	calcular_colec_lr1_2(self):
		conj={} #dict([(I,[]) for I in self.V])
		conj[self.S2+"prima"]=[([".",self.S2],["$"])]
		self.cerradura2(conj)
		del self.colec_lr0[:]
		self.colec_lr0.append(conj)
		sig=ult=0
		while sig<=ult:
			fila_ira={}
			for X in self.T2+self.V2:
				conj=self.ir_a2(self.colec_lr0[sig],X)
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
			self.tir_a2.append(fila_ira)
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
			vaux=[]
			taux=[]
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
					if alfa[0]!='lambda':
						for s in alfa:
							if s not in vaccesibles and s not in taccesibles:
								todos_accesibles = False
								break
					if todos_accesibles:
						if k in paux.keys():
							paux[k].append(x)
						else:
							paux[k]=[x]
		self.P={}
		for k,v in paux.iteritems():		
			self.P[k]=v
		self.V = vaccesibles
		self.T = taccesibles
	def aumentar_gramatica2(self):
		self.P2[self.S2+"prima"]=[[self.S2]]
		self.V2.append(self.S2+"prima")
		aux_reglas={}
		for k,v in self.P2.iteritems():
			for alfa in v:
				enc_acc=False
				for i in range(len(alfa)):
					if alfa[i] in self.acciones_sem2:
						enc_acc=True
						if i<len(alfa)-1:
							m=self.nuevo_marcador(aux_reglas,alfa[i],True)
							if m not in self.V2:
								self.V2.append(m)
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
				if not enc_acc: # ez du aurkitzen inongo akzio semantikorik produkzio barruan
					if k in aux_reglas.keys():
						aux_reglas[k].append((alfa,""))
					else:
						aux_reglas[k]=[(alfa,"")]
		self.P2={}
		for k,v in aux_reglas.iteritems():		
			self.P2[k]=v
		while True: # goikoa errepikatzen da hainbat bidar, produkzio barruan inongo akzio semantikorik laga ez arte
			final = True
			aux_reglas={}
			for k,v in self.P2.iteritems():
				for x in v:
					alfa,acc_sem=x
					enc_acc=False
					for i in range(len(alfa)):
						if alfa[i] in self.acciones_sem2:
							enc_acc=True
							if i<len(alfa)-1:
								m=self.nuevo_marcador(aux_reglas,alfa[i],False)
								if m not in self.V2:
									self.V2.append(m)
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
						final = False # iteraketa berriro egin behar da, azkenengoan akzio bat regla baten barruan aurkitu delako
			self.P2={}
			for k,v in aux_reglas.iteritems():		
				self.P2[k]=v
			if final:
				break
		# goiko tratamendua egin ondoren gelditzen bada markadore bat erregela baten amaieran, azkenengo hau kendu egiten da eta bere akzio erregelaren akzio listara gehitzen da
		aux_reglas={}
		for k,v in self.P2.iteritems():
			for x in v:
				alfa,acc_sem=x
				# alfa[len(alfa)-1] (erregelaren azekenengo simboloa) markadore bat da?
				if alfa[-1] in self.V2 and len(self.P2[alfa[-1]])==1:
					beta,acc=self.P2[alfa[-1]][0]
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
		self.P2={}
		for k,v in aux_reglas.iteritems():		
			self.P2[k]=v
		self.eliminarSimbolosNoAccesibles2()
	def eliminarSimbolosNoAccesibles2(self):
		vaccesibles=[self.S2+"prima"]
		taccesibles=[]
		while True:
			vaux=[]
			taux=[]
			for k,v in self.P2.iteritems():
				if k in vaccesibles:
					for x in v:
						alfa,acc_sem=x
						if alfa!=['lambda']:
							for s in alfa:
								if s in self.V2 and s not in vaccesibles and s not in vaux:
									vaux.append(s)
								elif s in self.T2 and s not in taccesibles and s not in taux:
									taux.append(s)
			if len(vaux)==0 and len(taux)==0:
				break
			vaccesibles.extend(vaux)
			taccesibles.extend(taux)
		#eliminar las reglas de produccion que tengan simbolos no accesibles en su parte izda o dcha.
		paux={}
		for k,v in self.P2.iteritems():
			if k in vaccesibles:
				for x in v:
					alfa,acc_sem=x
					todos_accesibles=True
					if alfa[0]!='lambda':
						for s in alfa:
							if s not in vaccesibles and s not in taccesibles:
								todos_accesibles = False
								break
					if todos_accesibles:
						if k in paux.keys():
							paux[k].append(x)
						else:
							paux[k]=[x]
		self.P2={}
		for k,v in paux.iteritems():		
			self.P2[k]=v
		self.V2 = vaccesibles
		self.T2 = taccesibles
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
								if i!=201:
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
	def calcular_tabla_accion2(self):
		for i in range(len(self.colec_lr0)):
			accion={}
			for k,v in self.colec_lr0[i].iteritems():
				for x in v:
					alfa,s=x
					pos_punto=alfa.index(".")
					if pos_punto<len(alfa)-1 and alfa[pos_punto+1] in self.T2:
						if alfa[pos_punto+1] in accion.keys():
							print "La gramatica no es LR(1), conflicto en estado ",i," con simbolo ",alfa[pos_punto+1]," accion desplazar "
							return False
						elif alfa[pos_punto+1] in self.tir_a2[i].keys():
							accion[alfa[pos_punto+1]]=("desplazar",self.tir_a2[i][alfa[pos_punto+1]])
						else:
							print "No hay estado siguiente, desde estado ",i," con simbolo ",alfa[pos_punto+1]
							return False
			for k,v in self.colec_lr0[i].iteritems():
				for x in v:
					alfa,s=x
					pos_punto=alfa.index(".")
					if pos_punto==len(alfa)-1 or alfa[pos_punto+1]=='lambda':
						if k==self.S2+"prima" and s.count("$")>0:
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
			self.taccion2.append(accion)
		return True
	def nueva_pizda(self):
		l=self.pila_sem[-1]
		self.P2[l]=[]
		self.pila_sem.append([])
	def nuevo_simbolo(self):
		l=self.pila_sem.pop()
		x=self.pila_sem[-1]
		x.append(l)
		self.pila_sem[-1]=x
	def termina_regla(self):
		x=self.pila_sem.pop()
		if len(x)==0:
			x=['lambda']
		l=self.pila_sem.pop()
		self.P2[l].append(x)
	def nueva_pdcha(self):
		x=self.pila_sem.pop()
		if len(x)==0:
			x=['lambda']
		l=self.pila_sem[-1]
		self.P2[l].append(x)
		self.pila_sem.append([])	
	def guarda(self,l):
		self.pila_sem.append(l)
	def compone(self,l):
		self.pila_sem[-1]=self.pila_sem[-1]+l
	def vaciar_pila(self):
		del self.pila_sem[:]
	def poner_axioma(self):
		self.S2=self.pila_sem.pop()
	def poner_vbles(self):
		for i in range(len(self.pila_sem)):
			self.V2.append(self.pila_sem.pop())
	def nueva_accion(self):
		l=self.pila_sem.pop() # oraingoan pilaren goian akzio bat dago
		x=self.pila_sem[-1] # hor erregelaren eskumako aldearen simboloak gordetzen dira
		x.append(l)
		self.pila_sem[-1]=x  # alde batetik akzio hori erregelera gehitu egiten da eta bestetik (hurrengo instrukzioa) akzioen listara
		if l not in self.acciones_sem2:
			self.acciones_sem2.append(l)
	def poner_acciones(self):
		for i in range(len(self.pila_sem)):
			self.acciones_sem2.append(self.pila_sem.pop())
	def inicio_escaner(self,f1):
		f1.write("import string\n")
		f1.write("def LeerSigTerm(f,linea,c):\n")
		f1.write("\tif len(linea)==0:\n")
		f1.write("\t\treturn (\'$\',\'$\',\'\',0)\n")
		f1.write("\twhile(linea[c] in [\' \',\'\\t\',\'\\n\']):\n")
		f1.write("\t\tc+=1\n")
		f1.write("\t\tif c>=len(linea):\n")
		f1.write("\t\t\tlinea=f.readline()\n")
		f1.write("\t\t\tc=0\n")
		f1.write("\t\t\tif len(linea)==0:\n")
		f1.write("\t\t\t\treturn (\'$\',\'$\',\'\',0)\n")
		f1.write("\tlexema= \'\'\n")
		f1.write("\ttoken=\'error\'\n")
		f1.write("\tmemc=c\n")
	def codigo_literal(self,f1):
		lit=self.pila_sem.pop()
		token=self.pila_sem.pop()
		# el escaner esperara encontrar los caracteres o simbolos tal como le vienen
		n=1
		for j in range(n):
			f1.write("\t")
		f1.write("if token==\'error\':\n")
		n=2
		for j in range(n):
			f1.write("\t")
		f1.write("c=memc\n")
		for i in range(len(lit)):
			if lit[i]=='\\':
				pass
			else:
				for j in range(n):
					f1.write("\t")
				f1.write("if len(linea)>0 and linea[c]==\'"+lit[i]+"\':\n")
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("lexema+=linea[c]\n")
				for j in range(n):
					f1.write("\t")
				f1.write("c+=1\n")
				for j in range(n):
					f1.write("\t")
				f1.write("if c>=len(linea):\n")
				for j in range(n+1):
					f1.write("\t")
				f1.write("linea=f.readline()\n")
				for j in range(n+1):
					f1.write("\t")
				f1.write("c=0\n")
		for j in range(n):
			f1.write("\t")
		f1.write("token=\'"+token+"\'\n")
		self.T2.append(token)
	def poner_alternativa(self):
		alt1=self.pila_sem.pop()
		alt2=self.pila_sem.pop()
		self.pila_sem.append(("|",alt1,alt2))
	def poner_rango_guion(self):
		fin=self.pila_sem.pop()
		ini=self.pila_sem.pop()
		self.pila_sem.append(("-",ini,fin))
	def poner_declaracion(self):
		decl=self.pila_sem.pop()
		nombre=self.pila_sem.pop()
		self.decls[nombre]=decl
	def poner_cierre_positivo(self):
		elem=self.pila_sem.pop()
		self.pila_sem.append(('+',elem))
	def poner_cierre(self):
		elem=self.pila_sem.pop()
		self.pila_sem.append(('*',elem))
	def concatenacion(self):
		fin=self.pila_sem.pop()
		ini=self.pila_sem.pop()
		self.pila_sem.append((".",ini,fin))
	def recuperar_decl_ant(self):
		nombre=self.pila_sem.pop()
		self.pila_sem.append(self.decls[nombre])
	def poner_como_tupla(self):
		x=self.pila_sem.pop(),
		self.pila_sem.append(x)
	def preorden(self,decl,n,token,f1):
		if len(decl)==3:
			x,y,z=decl
			if x=="|":
				self.preorden(y,n,token,f1)
				self.preorden(z,n,token,f1)
			elif x=='.': # concatenacion
				self.preorden(y,n,token,f1)
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("if token==\'"+token+"\':\n")
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("token=\'error\'\n")	
				for j in range(n):
					f1.write("\t")
				f1.write("memc=c\n")
				self.preorden(z,n,token,f1)
			elif x=='-':
				for j in range(n):
					f1.write("\t")
				f1.write("c=memc\n")
				for j in range(n):
					f1.write("\t")
				f1.write("if len(linea)>0 and linea[c]>=\'"+y+"\' and linea[c]<=\'"+z+"\':\n")
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("lexema+=linea[c]\n")
				for j in range(n):
					f1.write("\t")
				f1.write("token=\'"+token+"\'\n")
		elif len(decl)==2:
			x,y=decl
			if x=='*':
				for j in range(n):
					f1.write("\t")
				f1.write("while True:\n")
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("token=\'continua\'\n")
				n2=n
				self.preorden(y,n,token,f1)
				n=n2
				for j in range(n):
					f1.write("\t")
				f1.write("if token ==\'"+token+"\':\n")				
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("token=\'continua\'\n")
				for j in range(n):
					f1.write("\t")
				f1.write("c+=1\n")
				for j in range(n):
					f1.write("\t")
				f1.write("if c>=len(linea):\n")
				for j in range(n+1):
					f1.write("\t")
				f1.write("linea=f.readline()\n")
				for j in range(n+1):
					f1.write("\t")
				f1.write("c=0\n")
				for j in range(n):
					f1.write("\t")
				f1.write("memc=c\n")
				n-=1
				for j in range(n):
					f1.write("\t")
				f1.write("else:\n")
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("token=\'"+token+"\'\n")
				for j in range(n):
					f1.write("\t")
				f1.write("break\n")
			elif x=='+':
				for j in range(n):
					f1.write("\t")
				f1.write("while True:\n")
				n+=1
				n2=n
				self.preorden(y,n,token,f1)
				n=n2
				for j in range(n):
					f1.write("\t")
				f1.write("if token==\'error\':\n")
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("break\n")
				n-=1
				for j in range(n):
					f1.write("\t")
				f1.write("elif token ==\'continua\':\n")				
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("token=\'"+token+"\'\n")
				for j in range(n):
					f1.write("\t")
				f1.write("break\n")
				n-=1
				for j in range(n):
					f1.write("\t")
				f1.write("else:\n")
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("token=\'continua\'\n")
				for j in range(n):
					f1.write("\t")
				f1.write("c+=1\n")
				for j in range(n):
					f1.write("\t")
				f1.write("if c>=len(linea):\n")
				for j in range(n+1):
					f1.write("\t")
				f1.write("linea=f.readline()\n")
				for j in range(n+1):
					f1.write("\t")
				f1.write("c=0\n")
				n-=1
				for j in range(n):
					f1.write("\t")
				f1.write("memc=c\n")
		else:
			lit=decl[0]
			for j in range(n):
				f1.write("\t")
			f1.write("c=memc\n")  # gordetako hasierako posizioa berreskuratu egiten da
			for i in range(len(lit)):
				for j in range(n):
					f1.write("\t")
				f1.write("if len(linea)>0 and linea[c]==\'"+lit[i]+"\':\n")
				n+=1
				for j in range(n):
					f1.write("\t")
				f1.write("lexema+=linea[c]\n")
				for j in range(n):
					f1.write("\t")
				f1.write("c+=1\n")
				for j in range(n):
					f1.write("\t")
				f1.write("if c>=len(linea):\n")
				for j in range(n+1):
					f1.write("\t")
				f1.write("linea=f.readline()\n")
				for j in range(n+1):
					f1.write("\t")
				f1.write("c=0\n")
			for j in range(n):
				f1.write("\t")
			f1.write("token=\'"+token+"\'\n")
	def codigo_declaracion(self,f1):
		nombre=self.pila_sem.pop()
		token=self.pila_sem.pop()
		n=1
		for j in range(n):
			f1.write("\t")
		f1.write("if token==\'error\':\n")
		n=2
		self.preorden(self.decls[nombre],n,token,f1)
		self.T2.append(token)
	def fin_escaner(self,f1):
		f1.write("\treturn (token,lexema,linea,c)\n")
		f1.close()
	def escribe_gestor_semantico(self):
		nombre="gestor_"+sys.argv[1][0:string.find(sys.argv[1],".")]+".py"
		f2=open(nombre,"w")
		f2.write("class TGestor:\n")
		f2.write("\tdef __init__(self):\n")
		f2.write("\t\tself.pila_sem=[]\n")
		f2.write("\t\tself.leido=[]\n")
		f2.write("\tdef guarda_lex(self,l):\n")
		f2.write("\t\tself.leido.append(l)\n")
		for acc in self.acciones_sem2:
			f2.write("\tdef "+acc+"(self):\n")
			f2.write("\t\tprint \'Ejecutar "+acc+"\'\n")
		f2.close()
	def escribe_parser(self):
		self.aumentar_gramatica2()
		nombre="parser_"+sys.argv[1][0:string.find(sys.argv[1],".")]+".py"
		f1=open(nombre,"w")
		f1.write("#!/usr/bin/env python\n")
		f1.write("import sys\n")
		f1.write("from escaner_"+sys.argv[1][0:string.find(sys.argv[1],".")]+" import LeerSigTerm\n")
		f1.write("from gestor_"+sys.argv[1][0:string.find(sys.argv[1],".")]+" import TGestor\n")
		f1.write("class G:\n")
		f1.write("\tdef __init__(self):\n")
		f1.write("\t\tself.P={")
		for k,v in self.P2.iteritems():
			f1.write("\'"+k+"\':[")
			for x in v:
				alfa,acc=x
				f1.write("([\'"+reduce(hacer_lista,alfa)+"\'],\'"+acc+"\'),")
			f1.write("],\n\t\t\t")
		f1.write("}\n")	
		self.calcularPrimeroAsc2()
		self.calcular_colec_lr1_2()
		self.escribe_gestor_semantico()
		#self.mostrar_elementos()
		self.calcular_tabla_accion2()
		f1.write("\t\tself.taccion=[")
		for x in self.taccion2:
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
		for x in self.tir_a2:
			f1.write("{")
			for k,v in x.iteritems():
				f1.write("\'"+k+"\':"+str(v)+",")
			f1.write("},\n            \t\t")
		f1.write("]\n")
		f1.write("\t\tself.f = open(sys.argv[1],\'r\')\n")
		f1.write("\tdef parserAscendente(self):\n")
		f1.write("\t\tGejec=TGestor()\n") 
		f1.write("\t\tpila=[0]\n")
		f1.write("\t\tlinea = self.f.readline()\n")
		f1.write("\t\tc=0\n")
		f1.write("\t\ta,l,linea,c = LeerSigTerm(self.f,linea,c)\n")
		f1.write("\t\tGejec.guarda_lex(l)\n")
		f1.write("\t\twhile True:\n")
		f1.write("\t\t\testado=pila[-1]\n")
		f1.write("\t\t\tif not a in self.taccion[estado].keys():\n")
		f1.write("\t\t\t\tprint \'Error, falta entrada en accion, estado \',estado,\' con \',a,\' lexema \',l\n")
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
		f1.write("\t\t\t\t\tif k[0] not in self.tir_a[pila[-1]].keys():\n")
		f1.write("\t\t\t\t\t\tprint \'Error:falta el estado al cual ir despues de reducir \',pila[-1],\' con \',k[0]\n")
		f1.write("\t\t\t\t\t\treturn False\n")
		f1.write("\t\t\t\t\tpila.append(self.tir_a[pila[-1]][k[0]])\n")
		f1.write("\t\t\t\t\t#ejecutar la accion semantica correspondiente a la regla reducida\n")
		f1.write("\t\t\t\t\tfor n,v in self.P.iteritems():\n")
		f1.write("\t\t\t\t\t\tif n==k[0]:\n")
		f1.write("\t\t\t\t\t\t\tfor x in v:\n")
		f1.write("\t\t\t\t\t\t\t\tp,acc_sem=x\n")
		f1.write("\t\t\t\t\t\t\t\tif r[k[0]]==p and acc_sem:\n")
		uno=True
		for acc in self.acciones_sem2:
			if uno:
				f1.write("\t\t\t\t\t\t\t\t\tif acc_sem==\'"+acc+"\':\n")
				uno=False
			else:
				f1.write("\t\t\t\t\t\t\t\t\telif acc_sem==\'"+acc+"\':\n")
			f1.write("\t\t\t\t\t\t\t\t\t\tGejec."+acc+"()\n")
		f1.write("\t\t\t\telif op==\'desplazar\':\n")
		f1.write("\t\t\t\t\tpila.append(r)\n")
		f1.write("\t\t\t\t\ta,l,linea,c = LeerSigTerm(self.f,linea,c)\n")
		f1.write("\t\t\t\t\tGejec.guarda_lex(l)\n")
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
					if k[0] not in self.tir_a[pila[-1]].keys():
						print "Error:falta el estado al cual ir despues de reducir ",pila[-1]," con ",k[0]
						return False
					pila.append(self.tir_a[pila[-1]][k[0]])
					#ejecutar la accion semantica correspondiente a la regla reducida
					for n,v in self.P.iteritems():
						if n==k[0]:
							for x in v:
								p,acc_sem=x
								if r[k[0]]==p and acc_sem:								
									#print "Ejecutar ",acc_sem,leido[-2]
									if acc_sem=="nueva_pizda":
										self.nueva_pizda()
									elif acc_sem=="nuevo_simbolo":
										self.nuevo_simbolo()
									elif acc_sem=="termina_regla":
										self.termina_regla()
									elif acc_sem=="nueva_pdcha":
										self.nueva_pdcha()
									elif acc_sem=="guarda":
										self.guarda(leido[-2])
									elif acc_sem=="compone":
										self.compone(leido[-2])
									elif acc_sem=="vaciar_pila":
										self.vaciar_pila()
									elif acc_sem=="poner_axioma":
										self.poner_axioma()
									elif acc_sem=="poner_vbles":
										self.poner_vbles()
									elif acc_sem=="poner_acciones":
										self.poner_acciones()
									elif acc_sem=="nueva_accion":
										self.nueva_accion()
									elif acc_sem=="inicio_escaner":
										nombre="escaner_"+sys.argv[1][0:string.find(sys.argv[1],".")]+".py"
										f1=open(nombre,"w")
										self.inicio_escaner(f1)
									elif acc_sem=="codigo_literal":
										self.codigo_literal(f1)
									elif acc_sem=="fin_escaner":
										self.fin_escaner(f1)
									elif acc_sem=="poner_alternativa":
										self.poner_alternativa()
									elif acc_sem=="poner_rango_guion":
										self.poner_rango_guion()
									elif acc_sem=="poner_declaracion":
										self.poner_declaracion()
									elif acc_sem=="poner_cierre_positivo":
										self.poner_cierre_positivo()
									elif acc_sem=="poner_cierre":
										self.poner_cierre()
									elif acc_sem=="concatenacion":
										self.concatenacion()
									elif acc_sem=="recuperar_decl_ant":
										self.recuperar_decl_ant()
									elif acc_sem=="poner_como_tupla":
										self.poner_como_tupla()
									elif acc_sem=="codigo_declaracion":
										self.codigo_declaracion(f1)
									elif acc_sem=="escribe_parser":
										self.escribe_parser()
					#self.mostrar_situacion(pila,"r por "+k[0]+"->"+reduce(concatenar,r[k[0]]),leido)
				elif op=="desplazar":
					pila.append(r)
					a,l = self.LeerSigTerm()
					leido.append(l)
					#self.mostrar_situacion(pila,"d"+str(r),leido)
				elif op=="aceptar" and a=='$':
					return True
				else:
					print "Error: la entrada continua y se ha llegado a un estado de aceptacion"
					return False
	def mostrar_reglas(self):
		print "V=",self.V
		print "T=",self.T
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
	def mostrar_reglas2(self):
		for k,v in self.P2.iteritems():
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
if __name__ == "__main__":				
	Glflp = G()
	Glflp.aumentar_gramatica()
	#Glflp.mostrar_reglas()
	Glflp.calcularPrimeroAsc()
	Glflp.calcular_colec_lr1()
	#Glflp.mostrar_elementos()
	if Glflp.calcular_tabla_accion():
		Glflp.parserAscendente()


class TGestor:
	def __init__(self):
		self.pila_sem =[]
		self.arbol=[]
		self.premisas=[]
	def mostrarFBC(self,i):
		if self.arbol[i]['op'] in ('conj_dis','impl','coimpl'):
			return (self.mostrarFBC(self.arbol[i]['li'])+self.arbol[i]['tipo']+self.mostrarFBC(self.arbol[i]['ld']))
		elif self.arbol[i]['op']=='neg':
			return ('~'+self.mostrarFBC(self.arbol[i]['li']))
		elif self.arbol[i]['op']=='agrup':
			return ('('+self.mostrarFBC(self.arbol[i]['li'])+')')
		elif self.arbol[i]['op']=='prop':
			return self.arbol[i]['tipo']
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
		print 'Ejecutar demostrarArgumento'
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
	def guardar(self,token,lexema):
		print 'Ejecutar guardar ',token,' ',lexema
		self.pila_sem.append((token,lexema))
	def nueva_premisa(self):
		print 'Ejecutar nueva_premisa'
		li=self.pila_sem.pop()
		self.premisas.append(li)
	def agrupar(self):
		print 'Ejecutar agrupar'
		li=self.pila_sem.pop()
		nodo={'op':'agrup','tipo':None,'li':li,'ld':None}
		self.arbol.append(nodo)
		self.pila_sem.append(self.arbol.index(nodo))
	def introd_prop(self,lexema):
		print 'Ejecutar introd_prop ',lexema
		nodo = {'op':'prop','tipo':lexema,'li':None,'ld':None}
		self.arbol.append(nodo)
		self.pila_sem.append(len(self.arbol)-1)
	def introd_neg(self):
		print 'Ejecutar introd_neg'
		li=self.pila_sem.pop()
		nodo={'op':'neg','tipo':None,'li':li,'ld':None}
		self.arbol.append(nodo)
		self.pila_sem.append(self.arbol.index(nodo))
	def introd_conec(self):
		print 'Ejecutar introd_conec'
		ld = self.pila_sem.pop()
		oper,tipo = self.pila_sem.pop() 
		li = self.pila_sem.pop()
		nodo = {'op':oper,'tipo':tipo,'li':li,'ld':ld}
		self.arbol.append(nodo)
		self.pila_sem.append(self.arbol.index(nodo))

import string
def LeerSigTerm(f,CarSgte):
	while(CarSgte in [' ','\t','\n']):
		CarSgte = f.read(1)
	if CarSgte=='':
		return ('$','$','')
	lexema= ''
	token='error'
	if token=='error':
		while True:
			if CarSgte>='a' and CarSgte<='z':
				lexema+=CarSgte
				token='prop'
			if token=='error':
				break
			elif token =='continua':
				token='prop'
				break
			else:
				token='continua'
				CarSgte=f.read(1)
	if token=='error':
		if CarSgte=='(':
			lexema+=CarSgte
			CarSgte=f.read(1)
			token='par_ab'
	if token=='error':
		if CarSgte==')':
			lexema+=CarSgte
			CarSgte=f.read(1)
			token='par_ce'
	if token=='error':
		if CarSgte==',':
			lexema+=CarSgte
			CarSgte=f.read(1)
			token='coma'
	if token=='error':
		if CarSgte=='=':
			lexema+=CarSgte
			CarSgte=f.read(1)
			if CarSgte=='>':
				lexema+=CarSgte
				CarSgte=f.read(1)
				token='flecha_doble'
	if token=='error':
		if CarSgte=='v':
			lexema+=CarSgte
			CarSgte=f.read(1)
			token='conj_dis'
		if CarSgte=='^':
			lexema+=CarSgte
			CarSgte=f.read(1)
			token='conj_dis'
	if token=='error':
		if CarSgte=='-':
			lexema+=CarSgte
			CarSgte=f.read(1)
			if CarSgte=='>':
				lexema+=CarSgte
				CarSgte=f.read(1)
				token='impl'
	if token=='error':
		if CarSgte=='<':
			lexema+=CarSgte
			CarSgte=f.read(1)
			if CarSgte=='-':
				lexema+=CarSgte
				CarSgte=f.read(1)
				if CarSgte=='>':
					lexema+=CarSgte
					CarSgte=f.read(1)
					token='coimpl'
	if token=='error':
		if CarSgte=='~':
			lexema+=CarSgte
			CarSgte=f.read(1)
			token='neg'
	return (token,lexema,CarSgte)

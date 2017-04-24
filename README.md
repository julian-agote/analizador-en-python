# analizador-en-python
Pertsonak erabiltzen ditugun hizkuntzek bezela, hizkuntza informatikuak, gramatika bat daukate. Hemen hitzegingo dugun gramatikek erregela sintaktikoak deitzen direnekin osatuak daude, eta erregela hauek eukiko duten forma, exemplu honen bezelakoak izango dira. 
Chomsky gramatikentzako klasifikazino bat asmatu zuen, hizkuntza informatikoen sailtasun parekoentzako nahikoa da, egoeraren dependentziarik ez duten gramatikak edo bigarren mailakoak. Hauen erregelak honako forma izaten dute: -> simboloaren ezkerrean aldagai bakar bat egongo da eta eskumaldean nahi haibat aldagai edo terminal. Esaldiak erregela hauetatik sortzeko modua izaten da, lehenbizi axioma deritzon aldagaiko erregela bat hautatu, erregela horretan eskuman agertzen diren aldagaiak, aldagia horien erregelen bitartez aldatzen joan, bakarrik terminalez edo hitzez oraturiko esaldi bat lortu arte. Ez dago esan beharrik kombinasiñuak nahi beste izan daitezkeela, según aldagia bakoitza beren edozein erregelakin aldatuz joan ezkero.
Adibidez lehen ordenako logikako demostraziñuak honako forma izaten dute a->b, (b^c)<->a,~c->a => c, ikusten dan moduan formulaz osatuta daude, => símbolo aurretik, komaz banatutuako formulak lehengaiak deritzanak, eta simboloaren ondoren formula bat agertzen da, demostraziñuaren ondorioa dena. Hemen esaldiak formulak osatutako demostraziñuak izango dira, eta gramatika moduan honako hau balioko du (ez da bakarra):
Erregela sintaktikoak
A->P premisa_berria => FCONJ premisa_berria saiatu_demostratzen
P->FCONJ LF
LF->coma premisa_berria FCONJ LF
FCONJ->FIMPL FCONJP
FCONJP->conj_dis guardar FIMPL sartu_konektiba FCONJP | lambda
FIMPL->G FIMPLP
FIMPLP->impl gorde G sartu_konektiba FIMPLP | coimpl gorde G sartu_konektiba FIMPLP | lambda
G->neg G sartu_negaziñua | ( FCONJ ) agrupar | prop sartu_proposizioa

Mayuskulas idatzitako hitzak, aldagaiak dira, ez dira zuzenki textuan agertuko, estruktura handiagoren bilketak dira, adibidez P ikusten da beste bi aldagaiez osatua dagoela FCONJ eta LF, FCONJ dago osatua … eta horrela rekurtsiboki jarraituko genuke. P premisen lista identifikatuko ditu, premisa bakoitza ondo eragindako formula bat delarik. Ondo eragindako formulak FCONJ aldagaiendatik sortuko dira…
Minuskulas idatzitako hitzak bestalde, alde batetik, textuan suzenki agertu leikien hitzak dira. Batzuk hitz baten baino gehiagoko agrupazioak izan daitezke, adibidez conj_dis ^ (ingelsez and) eta v (or) konektibak identifikatzen ditu. Eta beste aldetik prozesamenduaren funtsioen izenak (adibidez premisa_berria) izango dira. Kompiladoreak zuhaitz sintaktikoa eraikitzen batera prozesamenduko funtsio hauek exekutatuko ditu (hau kasu gehienetan balioko dau komputagailu memorian gordetzen joateko, kasu honetan adibidez demostraziñuaren formulak, gero hauen tratamendua egin ahal izateko).
Kurtso honen helburua programa informatiko baten funtzionamendua argitzea izango da.
Programa honek kompiladore sortzaile bat izango da. Kompiladorearen funtzioa, texto bat sarrera moduan onartuz, honen analisi sintaktikoa egitea, eta aldi berean, erregela sintaktikoekin prozesamenduren bat atzikita badago, hauek exekutatzia. Textuaren analisi sintaktikoa egiteko, idatzita dagoen hizkuntzaren erregela sintaktikoak jakin behar dira, horretarako kompiladore sortzaileari pasatu behar zaio, zeintzuk diren hizkuntza horren gramatikako erregelak. Programa honek beste programa informatiko bat sortuko du emaitza moduan (Kompiladorea alegia, kaxu bakoitzean hizkuntza batentzako balio dabena, goiko adibidearen kasuan, lehen ordenako logikaren hizkuntzan idatzitako demostraziñuendako)

Nola egiten du Kompiladoreak analisi sintaktikoa? Ba textua hitzetan zatituz, hortik aurrera joaten da zuhaitz moduko bat osatzen, lehen aipatutako erregelekin, zeinek zuhaitza osatzen dutenek, orden batian aplikatuz ezkero textua berriro lortzera eramango genituzkeena.
Programa honek koLRsor izena izango du eta pythonen idatzita dago. Goian esan dugun moduan, sarrera moduan fitxero batetan, gero kompiladoreak erabiliko duen gramatika, sartuko zaio. Fitxero hau zatitan banatuta egongo da, zati bakoitza bere esanahairekin. Adibidez erregela sintaktikoak %%ERREGELAK ondoren agertuko dira eta goiko adibidearen moduan idatziko dira. Hemen jarriko dugu holako fitxero baten osagaia:
%%DECLS
letra [a-z]
prop {letra}+
conj_dis (\^|v)
%%TERMS
prop {prop}
( "("
) ")"
coma ","
=> "=>"
conj_dis {conj_dis}
impl "->"
coimpl "<->"
neg "~"
%%ALDAGAIAK
A,P,LF,FCONJ,FCONJP,FIMPL,FIMPLP,G
%%AXIOMA
A
%%PROZESAMENDUAK
introd_conec,introd_neg,introd_prop,agrupar, premisa_berria,guardar,demostrarArgumento
%%ERREGELAK
A->P premisa_berria => FCONJ premisa_berria demostrarArgumento;
P->FCONJ LF;
LF->coma premisa_berria FCONJ LF |;
FCONJ->FIMPL FCONJP;
FCONJP->conj_dis guardar FIMPL introd_conec FCONJP |;
FIMPL->G FIMPLP;
FIMPLP->impl guardar G introd_conec FIMPLP|coimpl guardar G introd_conec FIMPLP|;
G->neg G introd_neg|( FCONJ ) agrupar|prop introd_prop;

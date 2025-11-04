# ***********************************************************************************
#   OpenGLBasico3D-V5.py
#       Autor: Márcio Sarroglia Pinho
#       pinho@pucrs.br
#   Este programa exibe dois Cubos em OpenGL
#   Para maiores informações, consulte
# 
#   Para construir este programa, foi utilizada a biblioteca PyOpenGL, disponível em
#   http://pyopengl.sourceforge.net/documentation/index.html
#
#   Outro exemplo de código em Python, usando OpenGL3D pode ser obtido em
#   http://openglsamples.sourceforge.net/cube_py.html
#
#   Sugere-se consultar também as páginas listadas
#   a seguir:
#   http://bazaar.launchpad.net/~mcfletch/pyopengl-demo/trunk/view/head:/PyOpenGL-Demo/NeHe/lesson1.py
#   http://pyopengl.sourceforge.net/documentation/manual-3.0/index.html#GLUT
#
#   No caso de usar no MacOS, pode ser necessário alterar o arquivo ctypesloader.py,
#   conforme a descrição que está nestes links:
#   https://stackoverflow.com/questions/63475461/unable-to-import-opengl-gl-in-python-on-macos
#   https://stackoverflow.com/questions/6819661/python-location-on-mac-osx
#   Veja o arquivo Patch.rtf, armazenado na mesma pasta deste fonte.
# 
# ***********************************************************************************
from OpenGL.GL import *
from OpenGL.GLUT import *
from OpenGL.GLU import *
from Ponto import Ponto

from ListaDeCoresRGB import *
import Texture as TEX

#from PIL import Image
import time
import random as ALE

import numpy as np
from PIL import Image


Angulo = 0.0

# Quantidade de ladrilhos do piso (inicializada em algum ponto no cadigo)
QtdX = 0
QtdZ = 0

AlturaViewportDeMensagens = 0.2
AnguloDeVisao = 90.0


# Representa o conteúdo de uma celula do piso
class Elemento:
    def __init__(self, tipo=0, cor_do_objeto=0, cor_do_piso=0, altura=0.0, texture_id=0):
        self.tipo = tipo
        self.cor_do_objeto = cor_do_objeto
        self.cor_do_piso = cor_do_piso
        self.altura = altura
        self.texture_id = texture_id


# Codigos que definem o tipo do elemento que está em uma calula
VAZIO = 0
PREDIO = 10
RUA = 20
COMBUSTIVEL = 30
VEICULO = 40

# Matriz que armazena informações sobre o que existe na cidade
Cidade = [[Elemento() for _ in range(100)] for _ in range(100)]

# Pontos de interesse
Observador = Ponto()
Alvo = Ponto()
TerceiraPessoa = Ponto()
PosicaoVeiculo = Ponto()

ComTextura = 0


# **********************************************************************
#
# # **********************************************************************
def ImprimeCidade():
    for i in range(QtdZ):
        for j in range(QtdX):
            print(Cidade[i][j].cor_do_piso, end=" ")
        print()
        

# **********************************************************************
# def InicializaCidade(qtd_x, qtd_z):
# Esta função será substituída por uma que lê a matriz que representa
# a cidade
# **********************************************************************
def InicializaCidade(qtd_x, qtd_z):
    global Cidade
    ALE.seed(100)
    for i in range(qtd_z):
        for j in range(qtd_x):
            # A cor do piso é aleatória (como no código original)
            Cidade[i][j].cor_do_piso = ALE.randint(0, 39) 
            Cidade[i][j].cor_do_objeto = White
            Cidade[i][j].tipo = VAZIO
    #ImprimeCidade()
    
    #Cidade[2][19].cor_do_piso = Black

# **********************************************************************
# def posiciona_em_terceira_pessoa():
#   Este método posiciona o observador fora do cenário, olhando para o
#   centro do mapa (ou para o veículo)
# As variáveis "TerceiraPessoa" e "PosicaoVeiculo" são setadas na INIT
# **********************************************************************
def posiciona_em_terceira_pessoa():
    global Observador, Alvo
    Observador = Ponto(TerceiraPessoa.x, TerceiraPessoa.y, TerceiraPessoa.z)  # Posiciona observador
    Alvo = Ponto(PosicaoVeiculo.x, PosicaoVeiculo.y, PosicaoVeiculo.z)        # Define alvo como o veículo

    Alvo.imprime("Posiciona - Veiculo:") 
    
      
# **********************************************************************
#  init()
#  Inicializa os parametros globais de OpenGL
#/ **********************************************************************
def init():
    global QtdX, QtdZ
    global TerceiraPessoa, PosicaoVeiculo
    global AnguloDeVisao

    glClearColor(0.0, 0.0, 1.0, 1.0)  # Fundo de tela amarelo
    
    glClearDepth(1.0)
    glDepthFunc(GL_LESS)

    glShadeModel(GL_SMOOTH)  # Ou GL_FLAT, se desejar
    glColorMaterial(GL_FRONT, GL_AMBIENT_AND_DIFFUSE)

    glEnable(GL_DEPTH_TEST)   # Ativa teste de profundidade
    #glEnable(GL_CULL_FACE)    # Ativa remoção de faces traseiras    

    glPolygonMode(GL_FRONT_AND_BACK, GL_FILL)

    glEnable(GL_NORMALIZE)  # Normaliza vetores normais

    # Quantidade de retângulos do piso vai depender do mapa (hardcoded aqui)
    QtdX = 20
    QtdZ = 20

    InicializaCidade(QtdX, QtdZ)

    # ImprimeCidade()

    # Define a posição do observador e do veículo com base no tamanho do mapa
    TerceiraPessoa = Ponto(QtdX / 2, 10, QtdZ * 1.1)
    PosicaoVeiculo = Ponto(QtdX / 2, 0, QtdZ / 2)

    posiciona_em_terceira_pessoa()

    TEX.LoadTexture("bricks.jpg") # esta serah a textura 0
    TEX.LoadTexture("Piso.jpg")   # esta serah a textura 1

    TEX.UseTexture (-1) # desabilita o uso de textura, inicialmente

    #image = Image.open("Tex.png")
    #print ("X:", image.size[0])
    #print ("Y:", image.size[1])
    #image.show()
    AnguloDeVisao = 90


# **********************************************************************
#
# **********************************************************************
def DesenhaPredio(altura):
    glPushMatrix()
    
    # Aplica escala para transformar o cubo em um prédio
    glScalef(0.2, altura, 0.2)
    
    # Move para cima (para alinhar a base do prédio na célula)
    glTranslatef(0, 1, 0)

    # Desenha um cubo sólido representando o prédio
    glutSolidCube(1)

    glPopMatrix()

# **********************************************************************
# def DesenhaLadrilhoTEX(id_textura):
# Desenha uma célula do piso aplciando a textura ativa.
# **********************************************************************
def DesenhaLadrilhoTEX(id_textura):

    # Seta a cor como branco pois vai desenha com textura
    glColor3f(1, 1, 1)   

    # Habilita a textura id_textura
    TEX.UseTexture(id_textura)

    # Desenha o poligono
    glBegin(GL_QUADS)
    glNormal3f(0, 1, 0)
    glTexCoord2f(0.0, 1.0)
    glVertex3f(-0.5, 0.0, -0.5)
    glTexCoord2f(0.0, 0.0)
    glVertex3f(-0.5, 0.0, 0.5)
    glTexCoord2f(1.0, 0.0)
    glVertex3f(0.5, 0.0, 0.5)
    glTexCoord2f(1.0, 1.0)
    glVertex3f(0.5, 0.0, -0.5)
    glEnd()

    # Deasabilita a textura
    TEX.UseTexture(-1)


# **********************************************************************
# DesenhaPoligonosComTextura()
# **********************************************************************
def DesenhaPoligonosComTextura():

    glPushMatrix()
    glTranslate(QtdX*0.2,1, QtdZ*0.8)
    glRotatef(Angulo,1,0,0)
    DesenhaLadrilhoTEX(0)    
    glPopMatrix()

    glPushMatrix()
    glTranslate(QtdX*0.6,1,QtdZ*0.8)
    glRotatef(45,1,0,0)
    DesenhaLadrilhoTEX(1)    
    glPopMatrix()

# **********************************************************************
# void DesenhaLadrilho(int corBorda, int corDentro)
# Desenha uma celula do piso.
# O ladrilho tem largula 1, centro no (0,0,0) e esta sobre o plano XZ
# **********************************************************************
def DesenhaLadrilho(corBorda, corDentro):
    glColor3f(0,0,1) # desenha QUAD preenchido
    defineCor(corDentro)
    glBegin ( GL_QUADS )
    glNormal3f(0,1,0)
    glVertex3f(-0.5,  0.0, -0.5)
    glVertex3f(-0.5,  0.0,  0.5)
    glVertex3f( 0.5,  0.0,  0.5)
    glVertex3f( 0.5,  0.0, -0.5)
    glEnd()

    
    glColor3f(1,1,1) # desenha a borda da QUAD 
    defineCor(corBorda)
    glLineWidth(3)
    glBegin ( GL_LINE_STRIP )
    glNormal3f(0,1,0)
    glVertex3f(-0.5,  0.0, -0.5)
    glVertex3f(-0.5,  0.0,  0.5)
    glVertex3f( 0.5,  0.0,  0.5)
    glVertex3f( 0.5,  0.0, -0.5)
    glEnd()
    glLineWidth(1)
    
# **********************************************************************
#
# **********************************************************************  
def DesenhaCidade(QtdX, QtdZ):
    
    ALE.seed(100)  # usa uma semente fixa para gerar sempre as mesmas cores no piso
    glPushMatrix()

    for x in range(QtdX):
        glPushMatrix()
        for z in range(QtdZ):
            DesenhaLadrilho(White, Cidade[z][x].cor_do_piso)
            glTranslated(0, 0, 1)
        
        # Aqui, os predios devem ser desenhados
        
        glPopMatrix()
        glTranslated(1, 0, 0)

    glPopMatrix()

# **********************************************************************
def DefineLuz():
    # Define cores para um objeto dourado
    LuzAmbiente = [0.4, 0.4, 0.4] 
    LuzDifusa   = [0.7, 0.7, 0.7]
    LuzEspecular = [0.9, 0.9, 0.9]
    #PosicaoLuz0  = [2.0, 3.0, 0.0 ]  # PosiÃ§Ã£o da Luz
    PosicaoLuz0  = [Alvo.x, Alvo.y, Alvo.z]
    Especularidade = [1.0, 1.0, 1.0]

    # ****************  Fonte de Luz 0

    glEnable ( GL_COLOR_MATERIAL )

    #Habilita o uso de iluminaÃ§Ã£o
    glEnable(GL_LIGHTING)

    #Ativa o uso da luz ambiente
    glLightModelfv(GL_LIGHT_MODEL_AMBIENT, LuzAmbiente)
    # Define os parametros da luz numero Zero
    glLightfv(GL_LIGHT0, GL_AMBIENT, LuzAmbiente)
    glLightfv(GL_LIGHT0, GL_DIFFUSE, LuzDifusa  )
    glLightfv(GL_LIGHT0, GL_SPECULAR, LuzEspecular  )
    glLightfv(GL_LIGHT0, GL_POSITION, PosicaoLuz0 )
    glEnable(GL_LIGHT0)

    # Ativa o "Color Tracking"
    glEnable(GL_COLOR_MATERIAL)

    # Define a reflectancia do material
    glMaterialfv(GL_FRONT,GL_SPECULAR, Especularidade)

    # Define a concentraÃ§Ã£oo do brilho.
    # Quanto maior o valor do Segundo parametro, mais
    # concentrado sera o brilho. (Valores validos: de 0 a 128)
    glMateriali(GL_FRONT,GL_SHININESS,51)


# **********************************************************************
#
# **********************************************************************
def PosicUser():
    global AspectRatio
    # Salva o tamanho da janela
    w = glutGet(GLUT_WINDOW_WIDTH)
    h = glutGet(GLUT_WINDOW_HEIGHT)

    glMatrixMode(GL_PROJECTION)
    glLoadIdentity()
    # Seta a viewport para ocupar toda a janela
    # glViewport(0, 0, w, h)
    #
    # glViewport(0, int(h * AlturaViewportDeMensagens), w, int(h - h * AlturaViewportDeMensagens))

    #print ("AspectRatio", AspectRatio)
    AspectRatio = w / h
    gluPerspective(AnguloDeVisao,AspectRatio,0.01,1500) # Projecao perspectiva

    glMatrixMode(GL_MODELVIEW)
    glLoadIdentity()
    gluLookAt(Observador.x, Observador.y, Observador.z,   # Posição do Observador
              Alvo.x, Alvo.y, Alvo.z,                      # Posição do Alvo
              0.0, 1.0, 0.0)                               # Vetor UP

# **********************************************************************
#  reshape( w: int, h: int )
#  trata o redimensionamento da janela OpenGL
# **********************************************************************
def reshape(w: int, h: int):
    global AspectRatio
	# Evita divisÃ£o por zero, no caso de uma janela com largura 0.
    if h == 0:
        h = 1
    # Ajusta a relacao entre largura e altura para evitar distorcao na imagem.
    # Veja funcao "PosicUser".
    
	# Reset the coordinate system before modifying
    glMatrixMode(GL_PROJECTION)
    glLoadIdentity()
    # Seta a viewport para ocupar toda a janela
    glViewport(0, 0, w, h)
    
    # Ajusta a viewport para ocupar a parte superior da janela
    glViewport(0, int(h * AlturaViewportDeMensagens), w, int(h - h * AlturaViewportDeMensagens))

    AspectRatio = w / h
    gluPerspective(AnguloDeVisao,AspectRatio,0.01,1500) # Projecao perspectiva
    # PosicUser()

# **********************************************************************
# Imprime o texto S na posicao (x,y), com a cor 'cor'
# **********************************************************************
def PrintString(S: str, x: int, y: int, cor: tuple):
    defineCor(cor) 
    glRasterPos3f(x, y, 0) # define posicao na tela
    
    for c in S:
        # GLUT_BITMAP_HELVETICA_10
        # GLUT_BITMAP_TIMES_ROMAN_24
        # GLUT_BITMAP_HELVETICA_18
        glutBitmapCharacter(GLUT_BITMAP_TIMES_ROMAN_24, ord(c))


# **********************************************************************
# Imprime as coordenadas do ponto P na posicao (x,y), com a cor 'cor'
# **********************************************************************
def ImprimePonto(P: Ponto, x: int, y: int, cor: tuple):
    S = f'({P.x:.2f}, {P.y:.2f})'
    PrintString(S, x, y, cor)

# **********************************************************************
# Esta funcao cria uam area 2D para escrever mensagens de texto na tela
# **********************************************************************
def DesenhaEm2D():
    ativar_luz = False

    if glIsEnabled(GL_LIGHTING):
        glDisable(GL_LIGHTING)
        ativar_luz = True

    glMatrixMode(GL_PROJECTION)
    glLoadIdentity()

    # Salva o tamanho da janela
    w = glutGet(GLUT_WINDOW_WIDTH)
    h = glutGet(GLUT_WINDOW_HEIGHT)

    # Define a área a ser ocupada pela mensagens dentro da Janela
    glViewport(0, 0, w, int(h * AlturaViewportDeMensagens))  # janela de mensagens fica na parte de baixo

    # Define os limites lógicos da área OpenGL dentro da janela
    glOrtho(0, 10, 0, 10, 0, 1)

    glMatrixMode(GL_MODELVIEW)
    glLoadIdentity()

    # Desenha linha que divide as áreas 2D e 3D
    defineCor(GreenCopper)
    glLineWidth(15)
    glBegin(GL_LINES)
    glVertex2f(0, 10)
    glVertex2f(10, 10)
    glEnd()

    PrintString("Esta area eh destinada a mensagens de texto. Veja a funcao DesenhaEm2D", 0, 8, White)

    PrintString("Amarelo", 0, 0, Yellow)
    PrintString("Vermelho", 4, 2, Red)
    PrintString("Verde", 5, 4, Green)

    # Restaura os parâmetros que foram alterados
    glMatrixMode(GL_PROJECTION)
    glLoadIdentity()
    glViewport(0, int(h * AlturaViewportDeMensagens), w, int(h - h * AlturaViewportDeMensagens))

    if ativar_luz:
        glEnable(GL_LIGHTING)

# **********************************************************************
# DesenhaCubo()
# Desenha o cenario
# **********************************************************************
def DesenhaCubo():
    glutSolidCube(1)


# **********************************************************************
# display()
# Funcao que exibe os desenhos na tela
# **********************************************************************
def display():
    global Angulo
    # Limpa a tela com  a cor de fundo
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT)

    DefineLuz()
    PosicUser()

    glMatrixMode(GL_MODELVIEW) 
   
    glPushMatrix()
    DesenhaCidade(QtdX,QtdZ)
    glPopMatrix()

    glPushMatrix()
    DesenhaPoligonosComTextura()
    glPopMatrix()

    DesenhaEm2D()    

    Angulo = Angulo + 1

    glutSwapBuffers()


# **********************************************************************
# animate()
# Funcao chama enquanto o programa esta ocioso
# Calcula o FPS e numero de interseccao detectadas, junto com outras informacoes
#
# **********************************************************************
# Variaveis Globais
nFrames, TempoTotal, AccumDeltaT = 0, 0, 0
oldTime = time.time()

def animate():
    global nFrames, TempoTotal, AccumDeltaT, oldTime

    nowTime = time.time()
    dt = nowTime - oldTime
    oldTime = nowTime

    AccumDeltaT += dt
    TempoTotal += dt
    nFrames += 1
    
    if AccumDeltaT > 1.0/30:  # fixa a atualizacao da tela em 30
        AccumDeltaT = 0
        glutPostRedisplay()


# **********************************************************************
#  keyboard ( key: int, x: int, y: int )
#
# **********************************************************************
ESCAPE = b'\x1b'
def keyboard(*args):
    global image, ComTextura
    #print (args)
    # If escape is pressed, kill everything.

    if args[0] == ESCAPE:   # Termina o programa qdo
        os._exit(0)         # a tecla ESC for pressionada

    if args[0] == b't' :
        ComTextura = 1 - ComTextura

    # ForÃ§a o redesenho da tela
    glutPostRedisplay()

# **********************************************************************
#  arrow_keys ( a_keys: int, x: int, y: int )   
# **********************************************************************

def arrow_keys(a_keys: int, x: int, y: int):
    if a_keys == GLUT_KEY_UP:         # Se pressionar UP
        pass
    if a_keys == GLUT_KEY_DOWN:       # Se pressionar DOWN
        pass
    if a_keys == GLUT_KEY_LEFT:       # Se pressionar LEFT
        pass
    if a_keys == GLUT_KEY_RIGHT:      # Se pressionar RIGHT
        pass

    glutPostRedisplay()

def mouse(button: int, state: int, x: int, y: int):
    glutPostRedisplay()

def mouseMove(x: int, y: int):
    glutPostRedisplay()

# ***********************************************************************************
# Programa Principal
# ***********************************************************************************


glutInit(sys.argv)
glutInitDisplayMode(GLUT_RGBA|GLUT_DEPTH | GLUT_RGB)
glutInitWindowPosition(0, 0)

# Cria a janela na tela, definindo o nome da
# que aparecera na barra de ti­tulo da janela.
glutInitWindowPosition(0, 0)
# Define o tamanho inicial da janela grafica do programa
glutInitWindowSize(900, 700)
wind = glutCreateWindow(b"Simulador de Cidade")


# executa algumas inicializacoes
init ()

# Define que o tratador de evento para
# o redesenho da tela. A funcao "display"
# sera chamada automaticamente quando
# for necessario redesenhar a janela
glutDisplayFunc(display)
glutIdleFunc (animate)

# o redimensionamento da janela. A funcao "reshape"
# Define que o tratador de evento para
# sera chamada automaticamente quando
# o usuario alterar o tamanho da janela
glutReshapeFunc(reshape)

# Define que o tratador de evento para
# as teclas. A funcao "keyboard"
# sera chamada automaticamente sempre
# o usuario pressionar uma tecla comum
glutKeyboardFunc(keyboard)
    
# Define que o tratador de evento para
# as teclas especiais(F1, F2,... ALT-A,
# ALT-B, Teclas de Seta, ...).
# A funcao "arrow_keys" sera chamada
# automaticamente sempre o usuario
# pressionar uma tecla especial
glutSpecialFunc(arrow_keys)

#glutMouseFunc(mouse)
#glutMotionFunc(mouseMove)


try:
    # inicia o tratamento dos eventos
    glutMainLoop()
except SystemExit:
    pass

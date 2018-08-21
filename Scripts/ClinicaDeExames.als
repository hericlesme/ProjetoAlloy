module Exames

-----------------------------------------------------------------------------------------------------------
--| Projeto de Alloy - Computação@UFCG
--|
--| 	Grupo 8 : Clínica de Exames
--|
--| 		Eddie Kaleb
--| 		Eduardo Macedo
--| 		Henrique Castro
--| 		Héricles Emanuel
--|
--| 	Cliente: Camila Carvalho
--| 	Professor: Tiago Massoni
-----------------------------------------------------------------------------------------------------------


-----------------------------------------------------------------------------------------------------------
--> Assinaturas
-----------------------------------------------------------------------------------------------------------

sig Clinica {
  enfermeiros : set Enfermeiro
}

-- Assinatura dos Pacientes 

abstract sig Paciente {} 

sig PacienteVermelho extends Paciente {}

sig PacienteLaranja extends Paciente {}

sig PacienteVerde extends Paciente {}

sig PacienteBranca extends Paciente {} 

-- Assinatura dos Enfermeiros

abstract sig Enfermeiro{
  pacientes : set Paciente
}

sig EnfermeiraChefe extends Enfermeiro {}

sig EnfermeiroTecnico extends Enfermeiro {}

sig Estagiario in EnfermeiroTecnico {}

sig Veterano in EnfermeiroTecnico {}

-----------------------------------------------------------------------------------------------------------
-->Funções
-----------------------------------------------------------------------------------------------------------

fun getEnfermeiroResponsavel[p : Paciente] : set Enfermeiro {
	Enfermeiro & p.~pacientes
}

fun getClinica[e : Enfermeiro] : set Clinica {
	Clinica & e.~enfermeiros
}

fun getPacientes[e : Enfermeiro]: set Paciente {
	Paciente & e.pacientes
}

fun getEnfermeiroChefeResponsavel[p : Paciente] : set EnfermeiraChefe {
	EnfermeiraChefe & p.~pacientes
}

-----------------------------------------------------------------------------------------------------------
--> Predicados
-----------------------------------------------------------------------------------------------------------

-- Predicados Clinica

pred umaClinica[] {
	#Clinica = 1
}

-- Predicados dos Pacientes

pred vermelhoLaranjaIndividual[] {
  all l : PacienteLaranja | lone getEnfermeiroResponsavel[l]
  all v : PacienteVermelho | lone getEnfermeiroResponsavel[v] 
}

-- Prediacos dos Enfermeiros 

pred quantidadeDeEnfermeiros[] {
  #Estagiario = 3
  #Veterano = 3
  #EnfermeiraChefe = 6
}

pred umEnfermeiroChefePorPacienteAtendido[] {
  all x, y : EnfermeiraChefe, p:Paciente {
	 p in getPacientes[x] && p in getPacientes[y] => x = y
  }
}

pred estagiarioUmPaciente[] {
  all e : Estagiario | lone getPacientes[e]
}

pred todoEnfermeiroEstaNaClinica[] {
  all e : Enfermeiro | one getClinica[e]
}

pred estagiarioOuExclusivoVeterano[] {
  no Estagiario & Veterano
}

-----------------------------------------------------------------------------------------------------------
--> Fatos
-----------------------------------------------------------------------------------------------------------

fact fatosClinica {
   umaClinica[]
}

fact fatosEnfermeiro {
  quantidadeDeEnfermeiros[]
  todoEnfermeiroEstaNaClinica[]
  estagiarioOuExclusivoVeterano[]
  estagiarioUmPaciente[]
  umEnfermeiroChefePorPacienteAtendido[] 
}

fact fatosPaciente {
  vermelhoLaranjaIndividual[]
}

-----------------------------------------------------------------------------------------------------------
--> Asserts
-----------------------------------------------------------------------------------------------------------

assert testeEstagiarioSoAtendeUmPaciente {
  all e : Estagiario | lone getPacientes[e]
}

check testeEstagiarioSoAtendeUmPaciente for 12

assert todosPacientesTemUmEnfermeiroChefe {
    all e : EnfermeiraChefe, p : Paciente {
	 p in getPacientes[e] => #{ getEnfermeiroChefeResponsavel[p] } = 1
    } 
}

check todosPacientesTemUmEnfermeiroChefe for 12

assert testePacienteVermelhoSoEAtendidoPorUm {
  all p : PacienteVermelho | lone getEnfermeiroResponsavel[p] 
}

check testePacienteVermelhoSoEAtendidoPorUm for 12

assert testePacienteLaranjaSoEAtendidoPorUm {
  all p:PacienteLaranja | lone getEnfermeiroResponsavel[p] 
}

check testePacienteLaranjaSoEAtendidoPorUm for 12

pred show[] {}

run show for 12

using JuMP, DataStructures

mutable struct nodo
  nivel::Int64
  Model::JuMP.Model
  inf::Float64
  sup::Float64
  x_relax::Vector{Float64}
  frac::Vector{Float64}
  x_int::Vector{Float64}
  status::Symbol
end

function fractional(x,var_bin)
  s = length(var_bin)
  frac = Array{Float64,1}(s)

  for i=1:s
    frac[i] = modf(x[var_bin[i]])[1]
  end
  return frac
end

function branch(x,var_bin)
  f,i = findmin(abs(x-0.5))
  return var_bin[i]
end

function poda(lista_,sense,liminf,limsup, P)
  L = size(lista_)[1]
  erase = []
  P_ = 0
  for l=1:L
    if lista_[l].status == :Infeasible
      erase = copy([erase;[l]])
      P_ = P_ + 1
    elseif lista_[l].frac == 0
      erase = copy([erase;[l]])
      P_ = P_ + 1
    elseif (sense == :Max && lista_[l].sup <= liminf) ||(sense == :Min && lista_[l].inf >= limsup)
       erase = copy([erase;[l]])
       P_ = P_ + 1
    end
  end
  P =copy(P + P_)
  deleteat!(lista_,erase)
  return  P
end

function deep(m::JuMP.Model,var_bin,frac, solver::MathProgBase.AbstractMathProgSolver = JuMP.UnsetSolver())
    m_ = deepcopy(m)
    N = 1
    liminf = []
    limsup = []
    obj = []
    x_best = []
    x = []
    k = 1
    sense = m.objSense
    status1 = []
    status2 = []
   time = 0

    while frac != zeros(length(var_bin))
      tic()
      m1 = deepcopy(m_)
      m2 = deepcopy(m_)
      i_ = branch(frac,var_bin)
      if mod(k,2) == 0

         m1.colUpper[i_] = 0
         status1 = solve(m1, relaxation=true)
         x = copy(m1.colVal)
         obj = copy(m1.objVal)
         frac = fractional(x,var_bin)
         m_ = deepcopy(m1)
      elseif  mod(k,2) == 1

        m2.colLower[i_] = 1
        status2 = solve(m2, relaxation=true)
        x = copy(m2.colVal)
        obj = copy(m2.objVal)
        frac = fractional(x,var_bin)
        m_ = deepcopy(m2)
      end
     time_aux = toc()
     time = time + time_aux
      if status1 == :Infeasible && status2 == :Optimal
        m_ = deepcopy(m2)
      elseif status2 == :Infeasible && status1 == :Optimal
        m_ = deepcopy(m1)
      elseif  status1 == :Infeasible && status2 == :Infeasible
      break
      end
      if time >= 120
        break
      end
      k = k + 1
      N = N + 1
    end


  if sense == :Max
    if frac == zeros(length(var_bin))
     liminf = copy(obj)
     x_best = copy(x)
    else
     liminf = -Inf
     N = Inf
   end
  else
    if frac == zeros(length(var_bin))
       limsup = copy(obj)
       x_best = copy(x)
    else
       limsup = Inf
       N = Inf
   end
  end

return liminf, limsup, x_best,N
end

function largura(lista,sense,var_bin,liminf,limsup)
  liminf_ = copy(liminf)
  limsup_ = copy(limsup)
  Podas_aux = 0
  AUX = []
  int_sol = []
  x_best = []
  IntSol = 0
  lista_aux = copy(lista)
  Nivel = 5000
  k = 1
  time = 0
  sol = []
  time_aux = 0
  Visit_ = 0
  Visit_aux = 0
   while k <= Nivel && IntSol == 0
     tic()
     L = length(lista_aux)
     Visit_aux = copy(L)
     for l=1:L
        filhos(lista_aux[l],lista_aux,var_bin,sense,liminf_,limsup_)
     end
     L = length(lista_aux)
     erase = []
     for l=1:L
       if lista_aux[l].nivel == k - 1
         erase = copy([erase;[l]])
       end
     end
     deleteat!(lista_aux,erase)
     liminf_, limsup_, AUX, int_sol, IntSol  = gap(lista_aux,sense,liminf_,limsup_,AUX,int_sol,IntSol)
     Podas_aux = poda(lista_aux,sense,liminf,limsup,Podas_aux)
     k = k + 1
     time_aux = toc()
     time = time + time_aux
     Visit_ = Visit_ + Visit_aux
     if time >= 350
       break
     end
   end
   if AUX != []
     if sense == :Max
         t,r = size(AUX)
         for i=1:t
           if liminf_ == AUX[i,1]
             x_best = AUX[i,2:end]
             sol = liminf_
           end
         end
       else
         t,r = size(AUX)
         for i=1:t
           if limsup_ == AUX[i,1]
             x_best = AUX[i,2:end]
             sol = limsup_
           end
         end
     end
   end
   if sense == :Max
     if IntSol == 0
        liminf_ = -Inf
    end
   else
     if IntSol == 0
        limsup_ = Inf
    end
   end
   return liminf_, limsup_, x_best, time, Podas_aux, k, sol, Visit_, IntSol
end


function filhos(pai,lista_,var_bin,sense,liminf,limsup)
  #############################################################################
  # Nodo filho 1
  #############################################################################
    m1 = deepcopy(pai.Model)
    frac = copy(pai.frac)
    i_ = branch(frac,var_bin)
    m1.colUpper[i_] = 0
    status = solve(m1, relaxation=true)
    x = copy(m1.colVal)
    obj = copy(m1.objVal)
    frac = fractional(x,var_bin)

    if sense == :Max
      sup = copy(obj)
      inf = liminf
    else
      inf = copy(obj)
      sup = limsup
    end

    if frac == zeros(length(var_bin))
      x_int = copy(x)
    else
      x_int = []
    end
  nivel = pai.nivel + 1
  filho1 = nodo(nivel,m1,inf,sup,x,frac,x_int,status)
  push!(lista_,filho1)

  #############################################################################
  # Nodo filho 2
  #############################################################################
  m2 = deepcopy(pai.Model)
  m2.colLower[i_] = 1
  status = solve(m2, relaxation=true)
  x = copy(m2.colVal)
  obj = copy(m2.objVal)
  frac = fractional(x,var_bin)

  if sense == :Max
    sup = copy(obj)
    inf = copy(liminf)
  else
    inf = copy(obj)
    sup = copy(limsup)
  end

  if frac  == zeros(length(var_bin))
    x_int = copy(x)
  else
    x_int = []
  end

  filho2 = nodo(nivel,m2,inf,sup,x,frac,x_int,status)
  push!(lista_,filho2)
return nothing
end

function selection(lista,sense,liminf,limsup)
  pai = []
  l = []
  L = length(lista)
  for i=1:L
    if sense == :Max && lista[i].sup == limsup
       pai = lista[i]
       l = i
    elseif sense == :Min && lista[i].inf == liminf
      pai = lista[i]
      l = i
    end
  end
  return pai, l
end

function gap(lista,sense,liminf,limsup,AUX,int_sol,IntSol)
  ##############################################################################
  # Gap
  ##############################################################################

  SUP = []
  INFI = []


  L = length(lista)
    if sense ==:Max
      for l=1:L
        if  lista[l].status != :Infeasible && lista[l].status != :Unbounded
          SUP = copy([SUP;[lista[l].sup]])
        end
        if lista[l].x_int != []
            int_sol = copy([int_sol;[lista[l].sup]])
            IntSol = IntSol + 1
            AUX = copy([AUX;Matrix([lista[l].sup lista[l].x_relax'])])
          else
            int_sol = copy([int_sol;[liminf]])
        end
      end
      limsup = maximum(SUP)
      liminf = maximum(int_sol)
    else
      for l=1:L
        if lista[l].status != :Infeasible && lista[l].status != :Unbounded
         INFI = copy([INFI;[lista[l].inf]])
       end
        if lista[l].x_int != []
          int_sol = copy([int_sol;[lista[l].inf]])
          IntSol = IntSol + 1
          AUX = copy([AUX;Matrix([lista[l].inf lista[l].x_relax'])])
        else
          int_sol = copy([int_sol;[limsup]])
        end
      end
      liminf = minimum(INFI)
      limsup = minimum(int_sol)
    end
    return liminf, limsup, AUX, int_sol,IntSol
end


function BNB(m::JuMP.Model, solver::MathProgBase.AbstractMathProgSolver = JuMP.UnsetSolver())

  #-----------------------------------------------------------------------------
  # Nodo raiz
  #-----------------------------------------------------------------------------
  # inicialização da Lista
  m.ext[:time] = []
  m.ext[:status] = []
  m.ext[:nodes] = []
  m.ext[:Podas] = []
  m.ext[:Iter] = []
  m.ext[:intsols] = []
  Tempo = 0
  lista = []
  sol = []
  x_best = []
  IntSol = 0
  AUX = []
  # Relaxação linear

  m_ = deepcopy(m)
  status = solve(m_, relaxation=true)
  x = copy(m_.colVal)
  obj = copy(m_.objVal)

  sense = m_.objSense

  index = m_.colCat
  var_bin = []
  for  i =1:size(index)[1]
    if index[i] == :Bin
      var_bin = copy([var_bin;[i]])
    end
  end

  frac = fractional(x,var_bin)

  if frac == zeros(length(var_bin))
    m.objVal = copy(obj)
    m.colVal = copy(x)
    m.objBound = copy(obj)
    m.ext[:time] = 0
    m.ext[:status] = status
    m.ext[:nodes] = 0
    m.ext[:Podas] = 0
    m.ext[:Iter] = 0
    m.ext[:intsols] = 1
    return nothing
  end

  if status == :Infeasible
    m.objVal = NaN
    m.colVal = []
    m.objBound = NaN
    m.ext[:time] = 0
    m.ext[:status] = status
    m.ext[:nodes] = 0
    m.ext[:Podas] = 0
    m.ext[:Iter] = 0
    m.ext[:intsols] = 0
    return nothing
  end

 liminf, limsup, x_best, Max_nivel = deep(m_,var_bin,frac)

 if x_best != []
   IntSol = 1
 end

  if sense == :Max
    sup = copy(obj)
    inf = copy(liminf)
    limsup = copy(obj)
  else
    inf = copy(obj)
    sup = copy(limsup)
    liminf = copy(obj)
  end

raiz = nodo(0,m_,inf,sup,x,frac,[],status)

# Dados iniciais
nivel = 1
ϵ = limsup - liminf
iter = 1

push!(lista, raiz)

Visit_ = 0
if x_best ==[]
  liminf_, limsup_, x_best, time, Podas_aux, iter_aux, sol, Visit_, IntSol = largura(lista,sense,var_bin,liminf,limsup)
  ϵ_aux = limsup_ - liminf_
  if x_best !=[] && ϵ_aux <= 1.0e-1
      m.objVal = sol
      m.colVal = x_best
      if sense == :Max
        m.objBound = limsup_
      else
        m.objBound = liminf_
      end
      m.ext[:time] = time
      m.ext[:status] = status
      m.ext[:nodes] = Visit_
      m.ext[:Podas] = Podas_aux
      m.ext[:Iter] = iter_aux
      m.ext[:intsols] = IntSol
      return nothing
  elseif x_best !=[] && ϵ_aux > 1.0e-1
      if sense == :Max
        liminf = copy(liminf_)
      else
        limsup = copy(limsup_)
      end
  end
end

L = 1
int_sol = []

ϵ = limsup - liminf
iter = 1
Visit = 0
Podas = 0

tempo_aux = 0

Max_iter =5000

while ϵ >= 1.0e-1 && iter <= Max_iter
  tic()
  #############################################################################
  # Seleção do problema da lista para fazer branch
  #############################################################################
  pai, l = selection(lista,sense,liminf,limsup)
  deleteat!(lista,l)
  Visit = Visit + 1 # Número do nós onde se fez branch
  #############################################################################
  # Adicionar os nós filhos do problema selecionado da lista
  #############################################################################
  filhos(pai,lista,var_bin,sense,liminf,limsup)
  #############################################################################
  # Atualização do lowere (upper bound) para o problema de Min (Max)
  #############################################################################
  liminf, limsup, AUX, int_sol, IntSol = gap(lista,sense,liminf,limsup,AUX,int_sol,IntSol)
  #############################################################################
  # Podas da árvore
  #############################################################################
  Podas = poda(lista,sense,liminf,limsup,Podas)
  #############################################################################
  # Atualização do upper (lower) bound pra o problema de Min (Max)
  #############################################################################
   L = size(lista)[1]
   ϵ = limsup - liminf # Atualização do ϵ e do x_best (melhor solução inteira)

    if AUX != []
      if sense == :Max
          t,r = size(AUX)
          for i=1:t
            if liminf == AUX[i,1]
              x_best = AUX[i,2:end]
              sol = liminf
            end
          end
        else
          t,r = size(AUX)
          for i=1:t
            if limsup == AUX[i,1]
              x_best = AUX[i,2:end]
              sol = limsup
            end
          end
      end
    end
    tempo_aux = toc()
    Tempo = Tempo + tempo_aux
    iter = copy(iter) + 1
    if Tempo >= 300
      break
    end
end


if iter - 1 == Max_iter &&  ϵ > 1.0e-1 && x_best != []
  status = :Subotimal
  if sense == :Max
    sol = copy(liminf)
  else
    sol = copy(limsup)
  end
elseif iter - 1 == Max_iter && x_best == []
  status = :unsolved
  sol = NaN
elseif lista == [] && x_best == []
  status = :Infeasible
  sol = NaN
else
  status = :Optimal
end
#############################################################################
# Prenchimento dos outputs
#############################################################################
m.objVal = sol
m.colVal = x_best
if sense == :Max
  m.objBound = limsup
else
  m.objBound = liminf
end
m.ext[:time] = Tempo
m.ext[:status] = status
m.ext[:nodes] = Visit
m.ext[:Podas] = Podas
m.ext[:Iter] = iter
m.ext[:intsols] = IntSol

return nothing

end

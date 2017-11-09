
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

function fractional(x)
  s = length(x)
  frac = Array{Float64,1}(s)

  for i=1:s[1]
    frac[i] = modf(x[i])[1]
  end
  return frac
end

function branch(x,var_bin)
  aux = Inf*ones(size(x))
  for i in var_bin
    aux[i] = x[i]
  end
  f,i = findmin(abs(aux-0.5))
  return i
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
  lista = copy(deleteat!(lista_,erase))
  return lista, P
end

function deep(m::JuMP.Model,var_bin,frac)
  m_ = copy(m)
    N = 1
    liminf = []
    limsup = []
    obj = []
    x_best = []
    x = []
    k = 1
    sense = m_.objSense
    status = :Optimal
    while frac != zeros(length(frac)) && status == :Optimal
      i_ = branch(frac,var_bin)
      if mod(k,2) == 0
         m_.colUpper[i_] = 0
         status = solve(m_, relaxation=true)
         x = copy(m_.colVal)
         obj = copy(m_.objVal)
         frac = fractional(x)
      else
        m_.colLower[i_] = 1
        status = solve(m_, relaxation=true)
        x = copy(m_.colVal)
        obj = copy(m_.objVal)
        frac = fractional(x)
      end
      k = k + 1
      N = N + 1
    end


  if sense == :Max
    if status == :Optimal
     liminf = copy(obj)
     x_best = copy(x)
    else
     liminf = -Inf
     N = Inf
   end
  else
    if status == :Optimal
       limsup = copy(obj)
       x_best = copy(x)
    else
       limsup = Inf
       N = Inf
   end
  end

return liminf, limsup, x_best,N
end

function filhos(pai,lista_,var_bin,sense,liminf,limsup)
  lista = copy(lista_)
  #############################################################################
  # Nodo filho 1
  #############################################################################
    m1 = copy(pai.Model)
    frac = copy(pai.frac)
    i_ = branch(frac,var_bin)
    m1.colUpper[i_] = 0
    status = solve(m1, relaxation=true)
    x = copy(m1.colVal)
    obj = copy(m1.objVal)
    frac = fractional(x)

    if sense == :Max
      sup = copy(obj)
      inf = liminf
    else
      inf = copy(obj)
      sup = limsup
    end

    if frac == zeros(length(x))
      x_int = copy(x)
    else
      x_int = []
    end
  nivel = pai.nivel + 1
  filho1 = nodo(nivel,m1,inf,sup,x,frac,x_int,status)
  push!(lista,filho1)

  #############################################################################
  # Nodo filho 2
  #############################################################################
  m2 = copy(pai.Model)
  m2.colLower[i_] = 1
  status = solve(m2, relaxation=true)
  x = copy(m2.colVal)
  obj = copy(m2.objVal)
  frac = fractional(x)

  if sense == :Max
    sup = copy(obj)
    inf = copy(liminf)
  else
    inf = copy(obj)
    sup = copy(limsup)
  end

  if frac == zeros(length(x))
    x_int = copy(x)
  else
    x_int = []
  end

  filho2 = nodo(nivel,m2,inf,sup,x,frac,x_int,status)
  push!(lista,filho2)
return lista
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

function gap(lista,sense,liminf,limsup,AUX,int_sol)
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
          AUX = copy([AUX;Matrix([lista[l].inf lista[l].x_relax'])])
        else
          int_sol = copy([int_sol;[limsup]])
        end
      end
      liminf = minimum(INFI)
      limsup = minimum(int_sol)
    end
    return liminf, limsup, AUX, int_sol
end


function BNB(m::JuMP.Model)

  #-----------------------------------------------------------------------------
  # Nodo raiz
  #-----------------------------------------------------------------------------
  # inicialização da Lista
  m.ext[:Tempo] = []
  m.ext[:status] = []
  m.ext[:Visit] = []
  m.ext[:Podas] = []
  Tempo = []
  lista = []
  sol = []
  x_best = []
  AUX = []
  # Relaxação linear
  tic()
  m_ = copy(m)
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

  frac = fractional(x)

  if frac == zeros(length(x))
    println("Solução inteira achada")
    m = copy(m_)
    return nothing
  end

  if status == :Infeasible
    println("Problema inviável")
    m = copy(m_)
    return nothing
  end

 liminf, limsup, x_best, Max_nivel = deep(m_,var_bin,frac)

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
L = 1
int_sol = []

ϵ = abs(limsup - liminf)
iter = 1
Visit = 0
Podas = 0

Max_iter =1000

while ϵ >= 1.0e-1 && iter <= Max_iter

  pai, l = selection(lista,sense,liminf,limsup)
  deleteat!(lista,l)
  Visit = Visit + 1

  lista  = filhos(pai,lista,var_bin,sense,liminf,limsup)

  liminf, limsup, AUX, int_sol = gap(lista,sense,liminf,limsup,AUX,int_sol)

  lista, Podas = poda(lista,sense,liminf,limsup,Podas)

   L = size(lista)[1]
   ϵ = limsup - liminf

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
    iter = copy(iter) + 1
end
Tempo = toc()

if iter - 1 == Max_iter &&  ϵ > 1.0e-1 && x_best != []
  status = :Subotimal
  if sense == :Max
    sol = copy(liminf)
  else
    sol = copy(limsup)
  end
elseif iter - 1 == Max_iter && x_best == []
  status = :Nosolutionfound
elseif lista == [] && x_best == []
  status = :Infeasible
else
  status = :Optimal
end

m.objVal = sol
m.colVal = x_best
m.objBound = maximum([ϵ 0])
m.ext[:Tempo] = Tempo
m.ext[:status] = status
m.ext[:Visit] = Visit
m.ext[:Podas] = Podas

return nothing

end

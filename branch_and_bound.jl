
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
  visit::Int64
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

function poda(lista_,sense,liminf,limsup,V)
  L = size(lista_)[1]
  Visit = []
  V_ = 0
  erase = []
  for l=1:L
    if lista_[l].status == :Infeasible
      erase = copy([erase;[l]])
    elseif lista_[l].frac == 0
      erase = copy([erase;[l]])
    elseif (sense == :Max && lista_[l].sup <= liminf) ||(sense == :Min && lista_[l].inf >= limsup)
       erase = copy([erase;[l]])
     elseif lista_[l].visit == 1
      erase = copy([erase;[l]])
      V_ = copy(V_) + 1
    end
  end
  Visit = V_ + V
  lista = copy(deleteat!(lista_,erase))
  return lista, Visit
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


function BNB(m::JuMP.Model)

  #-----------------------------------------------------------------------------
  # Nodo raiz
  #-----------------------------------------------------------------------------
  # inicialização da Lista
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
    return m_
  end

  if status == :Infeasible
    println("Problema inviável")
    return m_
  end

 liminf, limsup, x_best, Max_iter = deep(m_,var_bin,frac)

  if sense == :Max
    sup = copy(obj)
    inf = copy(liminf)
    limsup = copy(obj)
  else
    inf = copy(obj)
    sup = copy(limsup)
    liminf = copy(obj)
  end

raiz = nodo(0,m_,inf,sup,x,frac,[],status,0)

# Dados iniciais
nivel = 1
ϵ = limsup - liminf
iter = 1

push!(lista, raiz)
L = 1
int_sol = []

ϵ = limsup - liminf
iter = 1
Visit = 0

if Max_iter  >= 50
  Max_iter = 10
end

while ϵ >= 1.0e-1 && iter <= Max_iter && lista != []


  for l=1:L

    #############################################################################
    # Nodo filho 1
    #############################################################################

      m1 = copy(lista[l].Model)
      frac = copy(lista[l].frac)
      i_ = branch(frac,var_bin)
      m1.colUpper[i_] = 0
      status = solve(m1, relaxation=true)
      x = copy(m1.colVal)
      obj = copy(m1.objVal)
      frac = fractional(x)

      if sense == :Max
        sup = copy(obj)
        if frac == zeros(length(x))
         inf = copy(obj)
        else
         inf = copy(liminf)
        end
      else
        inf = copy(obj)
        if frac == zeros(length(x))
        sup = copy(obj)
        else
        sup = copy(limsup)
        end
      end

      if frac == zeros(length(x))
        x_int = copy(x)
      else
        x_int = []
      end

    filho1 = nodo(nivel,m1,inf,sup,x,frac,x_int,status,0)
    push!(lista,filho1)

    #############################################################################
    # Nodo filho 2
    #############################################################################
    m2 = copy(lista[l].Model)
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

    filho2 = nodo(nivel,m2,inf,sup,x,frac,x_int,status,0)
    push!(lista,filho2)
    lista[l].visit = 1
  end
  ##############################################################################
  # Gap
  ##############################################################################

  SUP = []
  INFI = []

  L = size(lista)[1]
    if sense ==:Max
      for l=1:L
        if lista[l].nivel == nivel && lista[l].status != :Infeasible
          SUP = copy([SUP;[lista[l].sup]])
        end
        if lista[l].x_int != []
            int_sol = copy([int_sol;[lista[l].inf]])
            AUX = copy([AUX;Matrix([lista[l].inf lista[l].x_relax'])])
          else
            int_sol = copy([int_sol;[liminf]])
        end
      end
      limsup = minimum(SUP)
      liminf = maximum(int_sol)
    else
      for l=1:L
        if lista[l].nivel == nivel && lista[l].status != :Infeasible
         INFI = copy([INFI;[lista[l].inf]])
       end
        if lista[l].nivel == nivel && lista[l].x_int != []
          int_sol = copy([int_sol;[lista[l].sup]])
          AUX = copy([AUX;Matrix([lista[l].sup lista[l].x_relax'])])
        else
          int_sol = copy([int_sol;[limsup]])
        end
      end
      liminf = maximum(INFI)
      limsup = minimum(int_sol)
    end


    lista,Visit = poda(lista,sense,liminf,limsup,Visit)

    L = size(lista)[1]
   ϵ = limsup - liminf

     nivel = nivel + 1

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

liminf_ = []
limsup_ = []

if ϵ >= 1.0e-1 &&  iter > Max_iter && lista != []
  l = rand(collect(1:size(lista)[1]))
  liminf_, limsup_, x_best_ = deep(lista[l].Model,var_bin,lista[l].frac)
  if sense == :Max && liminf_ >= liminf
    liminf = copy(liminf_)
    x_best = copy(x_best_)
  elseif sense == :Min && limsup_ <= limsup
    limsup = copy(limsup_)
    x_best = copy(x_best_)
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
  status = :Nosolutionfound
else
  status = :Optimal
end
m.objVal = sol
m.colVal = x_best
m.objBound = maximum([ϵ;0])
Tempo = toc()
return m,status,Tempo, Visit

end

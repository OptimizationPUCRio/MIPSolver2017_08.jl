
using JuMP, DataStructures

mutable struct nodo
  nivel::Int64
  model::JuMP.Model
  inf::Float64
  sup::Float64
  x_relax::Vector{Float64}
  frac::Vector{Float64}
  x_int::Vector{Float64}
  status::Symbol
  visit::Int64
end

function fractional(x)
  s = size(x)
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

function poda(lista_,sense,liminf,limsup)
  L = size(lista_)[1]
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
    end
  end
  lista = copy(deleteat!(lista_,erase))
  return lista
end

function BNB(model::JuMP.Model)

  #-----------------------------------------------------------------------------
  # Nodo raiz
  #-----------------------------------------------------------------------------
  # inicialização da Lista

  lista = []
  x_best = []
  sol = []
  AUX = []
  # Relaxação linear

  status = solve(model, relaxation=true)
  x = copy(model.colVal)
  obj = copy(model.objVal)

  sense = model.objSense

  index = model.colCat
  var_bin = []
  for  i =1:size(index)[1]
    if index[i] == :Bin
      var_bin = copy([var_bin;[i]])
    end
  end

  frac = fractional(x)

  if frac == zeros(size(x))
    println("Solução inteira achada")
    x_best = copy(x)
    sol = copy(obj)
    return sol,x_best
  end

  if status == :Infeasible
    println("Problema inviável")
  end

  if sense == :Max
    sup = copy(obj)
    inf = -Inf
    limsup = copy(obj)
    liminf = -Inf
  else
    inf = copy(obj)
    sup = Inf
    limsup = Inf
    liminf = copy(obj)
  end

raiz = nodo(0,model,inf,sup,x,frac,[],status,0)

# Dados iniciais
nivel = 1
ϵ = limsup - liminf
iter = 1

push!(lista, raiz)
L = 1
int_sol = []

ϵ = limsup - liminf

while ϵ >= 1.0e-10


  for l=1:L

    #############################################################################
    # Nodo filho 1
    #############################################################################

      m = copy(lista[l].model)
      frac = copy(lista[l].frac)
      i_ = branch(frac,var_bin)
      m.colUpper[i_] = 0
      status = solve(m, relaxation=true)
      x = copy(m.colVal)
      obj = copy(m.objVal)
      frac = fractional(x)

      if sense == :Max
        sup = copy(obj)
        if frac == zeros(size(x))
         inf = copy(obj)
        else
         inf = -Inf
        end
      else
        inf = copy(obj)
        if frac == zeros(size(x))
        sup = copy(obj)
        else
        sup = Inf
        end
      end

      if frac == zeros(size(x))
        x_int = copy(x)
      else
        x_int = []
      end

    raiz = nodo(nivel,m,inf,sup,x,frac,x_int,status,0)
    push!(lista,raiz)

    #############################################################################
    # Nodo filho 2
    #############################################################################
    m = lista[l].model
    m.colLower[i_] = 1
    status = solve(m, relaxation=true)
    x = copy(m.colVal)
    obj = copy(m.objVal)
    frac = fractional(x)

    if sense == :Max
      sup = copy(obj)
      if frac == zeros(size(x))
       inf = copy(obj)
      else
       inf = -Inf
      end
    else
      inf = copy(obj)
      if frac == zeros(size(x))
      sup = copy(obj)
      else
      sup = Inf
      end
    end

    if frac == zeros(size(x))
      x_int = copy(x)
    else
      x_int = []
    end

    raiz = nodo(nivel,m,inf,sup,x,frac,x_int,status,0)
    push!(lista,raiz)
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
            int_sol = copy([int_sol;[-Inf]])
        end
      end
      limsup = maximum(SUP)
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
          int_sol = copy([int_sol;[Inf]])
        end
      end
      liminf = minimum(INFI)
      limsup = minimum(int_sol)
    end


    lista = copy(poda(lista,sense,liminf,limsup))
    L = size(lista)[1]
   ϵ = limsup - liminf

     nivel = nivel + 1

    if AUX != []
      if sense == :Max
          t,r = size(AUX)
          for i=1:t
            if liminf == AUX[i,1]
              x_best = Matrix(AUX[i,2:end]')'
              sol = liminf
            end
          end
        else
          t,r = size(AUX)
          for i=1:t
            if limsup == AUX[i,1]
              x_best = Matrix(AUX[i,2:end]')'
              sol = limsup
            end
          end
      end
    end

end

return sol,x_best

end

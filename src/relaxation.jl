importall JuMP, Gurobi, LightGraphs, Polynomials, Roots, Combinatorics
using Plots
pyplot()

function extract_data(model::JuMP.Model)
    c = JuMP.prepAffObjective(model)

    xlb = copy(model.colLower)
    xub = copy(model.colUpper)

    return c, xlb, xub
end

function lagrange(m::JuMP.Model,n)
  c, xlb, xub = extract_data(m)
  c = float(c)
  c_ = copy(c)
  #number_of_edges = length(c)
  #x = variable(Int)
  #n = Int(fzero(x^2 - x - 2*number_of_edges, 1.0))
  number_of_edges = Int((n^2 - n)/2)

  ind_fixas_0 = find(xub + xlb .== 0)
  ind_fixas_1 = find(xub + xlb .== 2)

  c[ind_fixas_0] = Inf
  c[ind_fixas_1] = -Inf

  distmx = cost_matrix(c,n)
  distmx_ = cost_matrix(c_,n)

  g = Graph()
  add_vertices!(g,n)
  e = create_edges(n,number_of_edges)

  for i=1:number_of_edges
    if i ∈ ind_fixas_1
      add_edge!(g,e[i,1],e[i,2])
    end
  end

  for i=1:n
    δ = degree(g,i)
    if δ > 2
      #m.objVal = :Infeasible
      #m.colVal = NaN
      #return nothing
      print("there is a problem")
    end
  end

  S = vcat([collect(combinations(2:n,i)) for i=1:n]...)
  s = length(S)
  for i=1:s
    if length(S[i]) >= 2
        sub_graph = induced_subgraph(g,S[i])[1]
        if ne(sub_graph) > nv(sub_graph) - 1
          #m.objVal = :Infeasible
          #m.colVal = NaN
          #return nothing
          print("there is a problem")
          #break
        end
    end
  end

  for i=1:number_of_edges
    if i ∉ ind_fixas_0
      add_edge!(g,e[i,1],e[i,2])
    end
  end

  V = copy(neighbors(g,1))
  for v in V
    rem_edge!(g,1,v)
  end

  ω = initial_tour(n,distmx)[1]
  #ω = 300
  u = zeros(n)
  iter = 1
  max_iter = 10000
  x = []
  z = []
  test = zeros(max_iter)
  y = Array{Float64,1}(n)
  c_e = Array{Float64,1}(number_of_edges)
  c_e_ = Array{Float64,1}(number_of_edges)
  while iter <= max_iter
    for i=1:number_of_edges
        c_e[i] = c[i] - u[e[i,1]] - u[e[i,2]]
        c_e_[i] = c[i] - u[e[i,1]] - u[e[i,2]]
    end

    distmx = cost_matrix(c_e,n)
    distmx_ = cost_matrix(c_e_,n)

    tree = kruskal_mst(g,distmx)
    cost = []
    for i=2:n
      cost_ = (distmx_[1,i],[1,i])
      cost = copy([cost;[cost_]])
    end
    sort!(cost, by = x -> x[1])

    g_tree = Graph()

    add_vertices!(g_tree, nv(g))

    for i in 1:length(tree)
      add_edge!(g_tree,tree[i])
    end

    k = 0
    for j=1:n - 1
      if j ∈ ind_fixas_1
         add_edge!(g_tree, Edge(cost[j][2][1],cost[j][2][2]))
         k = k +1
         if k == 2
           break
         end
      end
    end
    if k !=2
      for j=1:n - 1
        if j ∉ ind_fixas_0
           add_edge!(g_tree, Edge(cost[j][2][1],cost[j][2][2]))
           k = k +1
           if k == 2
             break
           end
        end
      end
    end

    for i=1:n
      y[i] = 2 - degree(g_tree,i)
    end
    z = (sum(full(adjacency_matrix(g_tree)).*distmx_))/2 +  2*sum(u)
    x = vcat([diag(full(adjacency_matrix(g_tree)),i) for i=1:n-1]...)
    u =  u + ((ω - z)/(sum(y[i]^2 for i=1:n)))*y
    if ω - z <= 5e-1
      break
    end
    test[iter]=z
    iter = iter+1
  end
  return z, x
end

function create_edges(n,number_of_edges) # Cria as arestas a partir da Matriz de Adjacencia

  e = zeros(number_of_edges,2)
  k=1;
  for i=1:n
    for j=i+1:n
      e[k,1]=i
      e[k,2]=j
      k = k+1
    end
  end
  return round(Int64,e)
end

function initial_tour(n,distmx)
  tour = Graph()
  add_vertices!(tour,n)
  t  = ne(tour)
  i = 1
  j = []
  visit = []
  while t < n - 1
    push!(visit,i)
    cost_ = copy(distmx[i,:])
    cost = copy(cost_)
    deleteat!(cost_,sort!(unique(visit)))
    val = findmin(cost_)[1]
    j = find(x->x==val,cost)[1]
    add_edge!(tour,i,j)
    i = copy(j)
    t = ne(tour)
  end
  add_edge!(tour,j,1)
   ω = sum(distmx.*full(adjacency_matrix(tour)))/2
   x = vcat([diag(full(adjacency_matrix(tour)),i) for i=1:n-1]...)
   return ω, x
end

function cost_matrix(c,n)
distmx = zeros(n,n)
  t = 0
  for i=1:n
      for j=i+1:n
        t = t+1
        distmx[i,j]=c[t]
      end
  end
  distmx = distmx + distmx'
  return distmx
end



#=

ind_fixas_0 = find(colUpper + colLower .== 0)
ind_fixas_1 = find(colUpper + colLower .== 2)

c[ind_fixas_0] = 1000
c[ind_fixas_1] = 0

distmx = zeros(n,n)
t = 0
for i=1:n
    for j=i+1:n
      t = t+1
      distmx[i,j]=c[t]
    end
end
distmx = distmx + distmx'

V = copy(neighbors(g,1))
for v in V
  rem_edge!(g,1,v)
end


tree = kruskal_mst(g,distmx)
cost = []
for i=2:n
  cost_ = (distmx[1,i],[1,i])
  cost = copy([cost;[cost_]])
end
sort!(cost, by = x -> x[1])

g_tree = Graph()

add_vertices!(g_tree, nv(g))

for i in 1:length(tree)
  add_edge!(g_tree,tree[i])
end
for j in 1:2
  add_edge!(g_tree, Edge(cost[j][2][1],cost[j][2][2]))
end
=#

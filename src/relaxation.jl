importall JuMP, Gurobi, LightGraphs, SimpleWeightedGraphs, Polynomials, Roots
using GraphPlot

function extract_data(model::JuMP.Model)
    c = JuMP.prepAffObjective(model)

    xlb = copy(model.colLower)
    xub = copy(model.colUpper)

    return c, xlb, xub
end

function lagrange(m::JuMP.Model)

  c, xlb, xu = extract_data(m)
  c_ = copy(c)
  number_of_edges = length(c)
  x = variable(Int)
  n = Int(fzero(x^2 - x - 2*number_of_edges, 1.0))

  ind_fixas_0 = find(xub + xlb .== 0)
  ind_fixas_1 = find(xub + xlb .== 2)

  c[ind_fixas_0] = 1000
  c[ind_fixas_1] = 0

  distmx = zeros(n,n)
  distmx_ = zeros(n,n)
  t = 0
  for i=1:n
      for j=i+1:n
        t = t+1
        distmx[i,j]=c[t]
        distmx_[i,j]=c_[t]
      end
  end
  distmx = distmx + distmx'
  distmx_ = distmx_ + distmx_'

  g = Graph()
  add_vertices!(g,n)
  e = create_edges(n,number_of_edges)

  for i=1:number_of_edges
    if i ∉ ind_fixas_0
      add_edge!(g,e[i,1],e[i,2])
    end
  end

  for i=1:n
    δ = degree(g,i)
    if δ < 2
      #m.objVal = :Infeasible
      #m.colVal = NaN
      #return nothing
      print("there is a problem")
    end
  end

  V = copy(neighbors(g,1))
  for v in V
    rem_edge!(g,1,v)
  end

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

  δ_1 = 0
  for i=1:n - 1
    if i ∈ ind_fixas_1
      δ_1 = δ_1 + 1
    end
  end

  if δ_1 > 2
    #m.objVal = :Infeasible
    #m.colVal = NaN
    #return nothing
    print("there is a problem")
  end


  k = 0
  for j=1:n - 1
    if j ∈ ind_fixas_1
       add_edge!(g_tree, Edge(cost[j][2][1],cost[j][2][2]))
       k = k +1
    end
  end
  if k !=2
    for j=1:n - 1
      if j ∉ ind_fixas_0
         add_edge!(g_tree, Edge(cost[j][2][1],cost[j][2][2]))
         k = k +1
      end
    end
  end



  μ = μ
  λ = maximum([λ - μ*(W-sum(w[i]*x[i] for i=1:3));0])
  k = k+1

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
   return ω
end






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

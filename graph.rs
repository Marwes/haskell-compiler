///Graph module, contains a simple graph structure which is when typechecking to find
///functions which are mutually recursive

use std::iter::repeat;
use std::cmp::min;

#[deriving(PartialEq, Show)]
pub struct VertexIndex(uint);
#[deriving(PartialEq)]
pub struct EdgeIndex(uint);

impl VertexIndex {
    fn get(&self) -> uint { let VertexIndex(v) = *self; v }
}
impl EdgeIndex {
    fn get(&self) -> uint { let EdgeIndex(v) = *self; v }
}

struct Vertex<T> {
    pub value: T,
    edges: Vec<EdgeIndex>
}
struct Edge<T> {
    from: VertexIndex,
    to: VertexIndex
}

pub struct Graph<T> {
    edges: Vec<Edge<T>>,
    vertices: Vec<Vertex<T>>
}

impl <T> Graph<T> {
    ///Creates a new graph
    pub fn new() -> Graph<T> {
        Graph { edges: Vec::new(), vertices: Vec::new() }
    }
    ///Creates a new vertex and returns the index which refers to it
    pub fn new_vertex(&mut self, value: T) -> VertexIndex {
        self.vertices.push(Vertex { edges:Vec::new(), value: value });
        VertexIndex(self.vertices.len() - 1)
    }
    
    ///Connects two vertices with an edge
    pub fn connect(&mut self, from: VertexIndex, to: VertexIndex) {
        self.vertices.get_mut(from.get()).edges.push(EdgeIndex(self.edges.len()));
        self.edges.push(Edge { from: from, to: to });
    }
    ///Returns the vertex at the index
    pub fn get_vertex<'a>(&'a self, v: VertexIndex) -> &'a Vertex<T> {
        self.vertices.get(v.get())
    }

    ///Returns the edge at the index
    pub fn get_edge<'a>(&'a self, edge: EdgeIndex) -> &'a Edge<T> {
        self.edges.get(edge.get())
    }

    ///Returns how many vertices are in the graph
    pub fn len(&self) -> uint {
        self.vertices.len()
    }
}

///Analyzes the graph for strongly connect components.
///Returns a vector of indices where each group is a separte vector
pub fn strongly_connected_components<T>(graph: &Graph<T>) -> Vec<Vec<VertexIndex>> {
    
    let mut tarjan = TarjanComponents { graph: graph, index: 1, stack: Vec::new(), connections: Vec::new(),
        valid: repeat(0).take(graph.len()).collect(),
        lowlink: repeat(0).take(graph.len()).collect()
    };
    

    for vert in range(0, graph.len()) {
        if *tarjan.valid.get(vert) == 0 {
            tarjan.strong_connect(VertexIndex(vert));
        }
    }

    tarjan.connections
        .into_iter()
        .map(|vec| -> Vec<VertexIndex> vec)
        .collect()
}

struct TarjanComponents<'a, T: 'a>{
    index: uint,
    graph: &'a Graph<T>,
    valid: Vec<uint>,
    lowlink: Vec<uint>,
    stack: Vec<VertexIndex>,
    connections: Vec<Vec<VertexIndex>>
}
///Implementation of "Tarjan's strongly connected components algorithm"
impl <'a, T> TarjanComponents<'a, T> {
    fn strong_connect(&mut self, v: VertexIndex) {
        *self.valid.get_mut(v.get()) = self.index;
        *self.lowlink.get_mut(v.get()) = self.index;
        self.index += 1;
        self.stack.push(v);

        for edge_index in self.graph.get_vertex(v).edges.iter() {
            let edge = self.graph.get_edge(*edge_index);
            if *self.valid.get(edge.to.get()) == 0 {
                self.strong_connect(edge.to);
                *self.lowlink.get_mut(v.get()) = min(*self.lowlink.get(v.get()), *self.lowlink.get(edge.to.get())); 
            }
            else if self.stack.iter().any(|x| *x == edge.to) {
                *self.lowlink.get_mut(v.get()) = min(*self.lowlink.get(v.get()), *self.valid.get(edge.to.get()));
            }
        }

        if self.lowlink.get(v.get()) == self.valid.get(v.get()) {
            let mut connected = Vec::new();
            loop {
                
                let w = self.stack.pop().unwrap();
                connected.push(w);
                if w == v {
                    break
                }
            }
            self.connections.push(connected);
        }
    }
}


#[test]
fn test_tarjan() {
    let mut graph = Graph::new();
    let v1 = graph.new_vertex(());
    let v2 = graph.new_vertex(());
    let v3 = graph.new_vertex(());
    graph.connect(v1, v2);
    graph.connect(v2, v1);
    graph.connect(v2, v3);
    let connections = strongly_connected_components(&graph);

    assert_eq!(connections.len(), 2);
    assert_eq!(connections[0], vec![v3]);
    assert_eq!(connections[1], vec![v2, v1]);
}

#[test]
fn test_tarjan2() {
    let mut graph = Graph::new();
    let v1 = graph.new_vertex(());
    let v2 = graph.new_vertex(());
    let v3 = graph.new_vertex(());
    let v4 = graph.new_vertex(());
    graph.connect(v1, v2);
    graph.connect(v2, v1);
    graph.connect(v2, v3);
    graph.connect(v3, v4);
    graph.connect(v4, v2);
    let connections = strongly_connected_components(&graph);

    assert_eq!(connections.len(), 1);
    assert_eq!(connections[0], vec![v4, v3, v2, v1]);
}

#[test]
fn test_tarjan3() {
    let mut graph = Graph::new();
    let v1 = graph.new_vertex(());
    let v2 = graph.new_vertex(());
    let v3 = graph.new_vertex(());
    let v4 = graph.new_vertex(());
    let v5 = graph.new_vertex(());
    graph.connect(v1, v2);
    graph.connect(v2, v1);
    graph.connect(v2, v3);
    graph.connect(v3, v4);
    graph.connect(v4, v3);
    graph.connect(v3, v5);
    let connections = strongly_connected_components(&graph);

    assert_eq!(connections.len(), 3);
    assert_eq!(connections[0], vec![v5]);
    assert_eq!(connections[1], vec![v4, v3]);
    assert_eq!(connections[2], vec![v2, v1]);
}

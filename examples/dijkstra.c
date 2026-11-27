// c2lean example: Dijkstra shortest paths, adjacency matrix, V = 9.
// Adapted for the verified subset: int instead of bool, no printf,
// flattened graph array (graph[u*9+v]).

#define V 9

int minDistance(int dist[], int sptSet[]) {
    int min = 2147483647, min_index = 0;
    for (int v = 0; v < V; v++)
        if (sptSet[v] == 0 && dist[v] <= min)
            min = dist[v], min_index = v;
    return min_index;
}

void dijkstra(int graph[], int dist[], int sptSet[], int src) {
    for (int i = 0; i < V; i++) {
        dist[i] = 2147483647;
        sptSet[i] = 0;
    }
    dist[src] = 0;
    for (int count = 0; count < V - 1; count++) {
        int u = minDistance(dist, sptSet);
        sptSet[u] = 1;
        for (int v = 0; v < V; v++)
            if (sptSet[v] == 0 && graph[u * V + v] != 0 &&
                dist[u] != 2147483647 &&
                dist[u] + graph[u * V + v] < dist[v])
                dist[v] = dist[u] + graph[u * V + v];
    }
}

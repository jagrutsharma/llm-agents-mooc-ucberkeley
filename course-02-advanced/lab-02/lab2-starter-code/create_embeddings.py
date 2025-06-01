#!/usr/bin/env python3

import os
from src.embedding_db import VectorDB
from src.embedding_models import OpenAIEmbeddingModel

def main():
    """
    Create embeddings for the documents in the documents folder.
    This script should be run before using the RAG functionality.
    """
    print("Creating embeddings for documents...")
    
    # Initialize embedding model
    embedding_model = OpenAIEmbeddingModel()
    
    # Initialize vector database
    vector_db = VectorDB(
        directory="documents",
        vector_file="database.npy",
        embedding_model=embedding_model
    )
    
    print("Embeddings created successfully!")
    print(f"Number of chunks: {len(vector_db.chunks)}")
    print(f"Embedding dimensions: {vector_db.embeddings.shape if vector_db.embeddings is not None else 'N/A'}")
    
    # Test the search functionality
    print("\nTesting search functionality...")
    test_queries = [
        "identity function",
        "minimum of three values",
        "implementing factorial",
        "proving boolean operations"
    ]
    
    for query in test_queries:
        print(f"\nQuery: '{query}'")
        top_chunks, top_scores = VectorDB.get_top_k(
            "database.npy", 
            embedding_model, 
            query, 
            k=1, 
            verbose=False
        )
        
        if top_chunks:
            print(f"Found {len(top_chunks)} result(s)")
            # Print a preview of the first result
            preview = top_chunks[0][:200] + "..." if len(top_chunks[0]) > 200 else top_chunks[0]
            print(f"Preview: {preview}")
            print(f"Score: {top_scores[0]:.4f}")
        else:
            print("No results found")
    
    print("\nEmbedding database is ready for use!")

if __name__ == "__main__":
    main() 
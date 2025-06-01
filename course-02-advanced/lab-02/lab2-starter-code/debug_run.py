#!/usr/bin/env python3

import os
import time
import sys
from src.main import main_workflow, get_problem_and_code_from_taskpath
from src.lean_runner import execute_lean_code

def debug_task(task_id="task_id_0"):
    """Test a single task with verbose debug output."""
    print(f"\n{'=' * 60}")
    print(f"DEBUG RUN for task {task_id}")
    print(f"{'=' * 60}")
    
    # Paths to task files
    task_path = f"tasks/{task_id}"
    
    # Read the problem description and Lean code template
    print(f"Reading task files from {task_path}...")
    problem_description, task_lean_code = get_problem_and_code_from_taskpath(task_path)
    
    print(f"\nProblem description:\n{problem_description[:200]}...")
    print(f"\nTask Lean code:\n{task_lean_code[:200]}...")
    
    # Run the workflow
    print("\nRunning main workflow...")
    start_time = time.time()
    
    # Use a try-except block to catch and display any errors
    try:
        result = main_workflow(problem_description, task_lean_code)
        workflow_time = time.time() - start_time
        print(f"Workflow completed in {workflow_time:.2f} seconds")
        
        # Extract the generated code and proof
        generated_code = result["code"]
        generated_proof = result["proof"]
        
        print(f"\nGenerated code:\n{generated_code}")
        print(f"\nGenerated proof:\n{generated_proof}")
        
        # Create the full Lean code with the generated code and proof
        print("\nCreating full Lean code...")
        full_lean_code = task_lean_code.replace("{{code}}", generated_code).replace("{{proof}}", generated_proof)
        
        # Execute the Lean code to check for errors
        print("\nExecuting Lean code...")
        execution_result = execute_lean_code(full_lean_code)
        
        if "executed successfully" in execution_result:
            print("\n✅ SUCCESS: Lean code executed successfully!")
        else:
            print(f"\n❌ FAILURE: Lean code execution failed with error:\n{execution_result}")
        
        return True
    
    except Exception as e:
        import traceback
        print(f"\n❌ ERROR: An exception occurred: {str(e)}")
        print("\nStacktrace:")
        traceback.print_exc()
        return False

if __name__ == "__main__":
    # Use command line argument if provided, otherwise default to task_id_0
    task_id = sys.argv[1] if len(sys.argv) > 1 else "task_id_0"
    debug_task(task_id) 
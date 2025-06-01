#!/usr/bin/env python3

import os
import time
import json
import sys
from src.main import main_workflow, get_problem_and_code_from_taskpath, get_unit_tests_from_taskpath
from src.lean_runner import execute_lean_code

def test_task(task_id):
    """Test a single task and report results."""
    print(f"\n{'=' * 60}")
    print(f"Testing task {task_id}")
    print(f"{'=' * 60}")
    
    # Paths to task files
    task_path = f"tasks/{task_id}"
    
    # Read the problem description and Lean code template
    print(f"Reading task files from {task_path}...")
    problem_description, task_lean_code = get_problem_and_code_from_taskpath(task_path)
    unit_tests = get_unit_tests_from_taskpath(task_path)
    
    print(f"Problem description length: {len(problem_description)} characters")
    print(f"Task Lean code length: {len(task_lean_code)} characters")
    print(f"Unit tests length: {len(unit_tests)} characters")
    
    # Run the workflow
    print("\nRunning main workflow...")
    start_time = time.time()
    try:
        result = main_workflow(problem_description, task_lean_code)
        workflow_time = time.time() - start_time
        print(f"Workflow completed in {workflow_time:.2f} seconds")
        
        # Extract the generated code and proof
        generated_code = result["code"]
        generated_proof = result["proof"]
        
        print(f"\nGenerated code: '{generated_code[:50]}...' ({len(generated_code)} chars)")
        print(f"Generated proof: '{generated_proof[:50]}...' ({len(generated_proof)} chars)")
        
        # Test the generated code and proof with unit tests
        print("\nTesting generated code and proof with unit tests...")
        generated_lean_code = task_lean_code.replace("{{code}}", generated_code).replace("{{proof}}", generated_proof)
        execution_result = execute_lean_code(generated_lean_code + f"\n\n{unit_tests}")
        
        if "executed successfully" in execution_result:
            print("\n✅ SUCCESS: Generated code and proof pass unit tests!")
            success = True
            error_message = None
        else:
            print("\n❌ FAILURE: Generated code or proof has errors with unit tests.")
            print(f"Error details: {execution_result[:200]}...")
            success = False
            error_message = execution_result[:500]
            
        return {
            "task_id": task_id,
            "success": success,
            "error": error_message,
            "time": workflow_time,
            "code_length": len(generated_code),
            "proof_length": len(generated_proof)
        }
            
    except Exception as e:
        print(f"\n❌ ERROR: An exception occurred: {str(e)}")
        import traceback
        traceback.print_exc()
        return {
            "task_id": task_id,
            "success": False,
            "error": str(e),
            "time": time.time() - start_time,
            "code_length": 0,
            "proof_length": 0
        }

def main():
    """Test all tasks individually."""
    all_task_ids = [
        "task_id_0", 
        "task_id_58", 
        "task_id_77", 
        "task_id_127", 
        "task_id_227", 
        "task_id_404", 
        "task_id_431", 
        "task_id_433", 
        "task_id_435", 
        "task_id_441", 
        "task_id_447"
    ]
    
    # Check if we should run a specific task
    if len(sys.argv) > 1 and sys.argv[1] in all_task_ids:
        all_task_ids = [sys.argv[1]]
        print(f"Running only task {sys.argv[1]}")
    
    results = {}
    
    for task_id in all_task_ids:
        result = test_task(task_id)
        results[task_id] = result
        
        # Save results after each task in case of crashes
        with open("task_results.json", "w") as f:
            json.dump(results, f, indent=2)
    
    # Print summary
    print("\n\n" + "=" * 60)
    print("SUMMARY OF RESULTS")
    print("=" * 60)
    success_count = 0
    
    for task_id, result in results.items():
        status = "✅ PASS" if result["success"] else "❌ FAIL"
        time_str = f"{result['time']:.2f}s" if "time" in result else "N/A"
        print(f"{task_id}: {status} (Time: {time_str})")
        if result["success"]:
            success_count += 1
    
    print(f"\nPassed {success_count}/{len(results)} tasks ({success_count/len(results)*100:.1f}%)")
    print("=" * 60)
    
    return results

if __name__ == "__main__":
    main() 
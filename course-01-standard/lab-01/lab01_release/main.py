from typing import Dict, List
from autogen import ConversableAgent
import sys
import os
import math

################# T O O L S #################

# Tool for getting reviews for a restaurant
def fetch_restaurant_data(restaurant_name: str) -> Dict[str, List[str]]:
    # TODO
    # This function takes in a restaurant name and returns the reviews for that restaurant. 
    # The output should be a dictionary with the key being the restaurant name and the value being a list of reviews for that restaurant.
    # The "data fetch agent" should have access to this function signature, and it should be able to suggest this as a function call. 
    # Example:
    # > fetch_restaurant_data("Applebee's")
    # {"Applebee's": ["The food at Applebee's was average, with nothing particularly standing out.", ...]}
    
    # pass
    reviews = {}
    normalized_restaurant_name = restaurant_name.lower()
    
    try:
        with open('restaurant-data.txt', 'r') as file:
            for line in file:
                name, review = line.strip().split('.', 1)
                normalized_name = name.lower()
                if normalized_name not in reviews:
                    reviews[normalized_name] = []
                reviews[normalized_name].append(review.strip())
    except FileNotFoundError:
        return {restaurant_name: ["No reviews found."]}
    
    return {restaurant_name: reviews.get(normalized_restaurant_name, ["No reviews found."])}

# Tool for getting unique restaurant names
def fetch_unique_restaurant_names() -> List[str]:
    # DONE
    # This function should return a list of unique restaurant names from the data file. 
    # The "data fetch agent" should have access to this function signature, and it should be able to suggest this as a function call. 
    # Example:
    # > fetch_unique_restaurant_names()
    # ["Applebee's", "Chick-fil-A", "In N Out", ...]
    unique_names = set()
    
    try:
        with open('restaurant-data.txt', 'r') as file:
            for line in file:
                name, _ = line.strip().split('.', 1)
                unique_names.add(name)
    except FileNotFoundError:
        return []
    
    return list(unique_names)

# Tool for calculating overall score
def calculate_overall_score(restaurant_name: str, food_scores: List[int], customer_service_scores: List[int]) -> Dict[str, float]:
    # DONE
    # This function takes in a restaurant name, a list of food scores from 1-5, and a list of customer service scores from 1-5
    # The output should be a score between 0 and 10, which is computed as the following:
    # SUM(sqrt(food_scores[i]**2 * customer_service_scores[i]) * 1/(N * sqrt(125)) * 10
    # The above formula is a geometric mean of the scores, which penalizes food quality more than customer service. 
    # Example:
    # > calculate_overall_score("Applebee's", [1, 2, 3, 4, 5], [1, 2, 3, 4, 5])
    # {"Applebee's": 5.048}
    # NOTE: be sure to that the score includes AT LEAST 3  decimal places. The public tests will only read scores that have 
    # at least 3 decimal places.
    
    N = len(food_scores)
    if N == 0 or len(customer_service_scores) != N:
        return {restaurant_name: 0.0}
    
    total_score = sum(math.sqrt(food_scores[i]**2 * customer_service_scores[i]) for i in range(N))
    overall_score = (total_score / (N * math.sqrt(125))) * 10
    formatted_score = round(overall_score, 3)
    return {restaurant_name: formatted_score}

def get_data_fetch_agent_prompt(restaurant_query: str) -> str:
    # DONE - ended up not using this
    # It may help to organize messages/prompts within a function which returns a string. 
    # For example, you could use this function to return a prompt for the data fetch agent 
    # to use to fetch reviews for a specific restaurant.
    pass

# DONE: feel free to write as many additional functions as you'd like.

################# M A I N #################

# Do not modify the signature of the "main" function.
def main(user_query: str):
    os.environ['OPENAI_API_KEY'] = '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'

    entrypoint_agent_system_message = """
                                        You are a capable supervisor and coordinator. 
                                        You are responsible for initiating chats with other agents.
                                    """ # TODO

    # example LLM config for the entrypoint agent
    llm_config = {"config_list": [{"model": "gpt-4o-mini", "api_key": os.environ.get("OPENAI_API_KEY")}]}
    
    # the main entrypoint/supervisor agent
    entrypoint_agent = ConversableAgent(
                                name = "entrypoint_agent", 
                                system_message=entrypoint_agent_system_message, 
                                llm_config=llm_config,
                                human_input_mode="NEVER")
    
    entrypoint_agent.register_for_execution(name="fetch_unique_restaurant_names")(fetch_unique_restaurant_names)
    entrypoint_agent.register_for_execution(name="fetch_restaurant_data")(fetch_restaurant_data)
    entrypoint_agent.register_for_execution(name="calculate_overall_score")(calculate_overall_score)
    
    # DONE
    # Create more agents here. 
    
    # The data fetch agent

    data_fetch_agent_system_message = """ 
        You are a data fetch agent. You are given a query to fetch reviews for a restaurant. Follow these steps:
        Step 1. Analyze the query, figure out the restaurant mentioned in the query.
        Step 2: The query may not have the exact name of the restaurant as in the data file.
        So, get all the unique restaurant names from the data file, and then figure out the closest match to the restaurant mentioned in the query.
        Step 3: Then fetch the reviews for that restaurant.
        Return all the reviews for the restaurant in a dictionary format.
    """

    data_fetch_agent = ConversableAgent(
                                name = "data_fetch_agent",
                                system_message = data_fetch_agent_system_message,
                                llm_config = llm_config,
                                code_execution_config=False,
                                human_input_mode="NEVER")
    
    data_fetch_agent.register_for_llm(name="fetch_unique_restaurant_names", description="Fetches the unique restaurant names.")(fetch_unique_restaurant_names)

    data_fetch_agent.register_for_llm(name="fetch_restaurant_data", description="Fetches the reviews for a specific restaurant.")(fetch_restaurant_data)

    # The review analysis agent

    review_analysis_agent_system_message = """ 
        You are a review analysis agent. You are given a set of reviews for a restaurant.
        Look at every single review and extract two scores from each review:

        food_score: the quality of food at the restaurant. This will be a score from 1-5.
        customer_service_score: the quality of customer service at the restaurant. This will be a score from 1-5.
        You should extract these two scores by looking for keywords in the review. 
        Each review has keyword adjectives that correspond to the score that the restaurant should get for its food_score and customer_service_score. 
        Here are the keywords you should look out for:

        Score 1/5 has one of these adjectives: awful, horrible, or disgusting.
        Score 2/5 has one of these adjectives: bad, unpleasant, or offensive.
        Score 3/5 has one of these adjectives: average, uninspiring, or forgettable.
        Score 4/5 has one of these adjectives: good, enjoyable, or satisfying.
        Score 5/5 has one of these adjectives: awesome, incredible, or amazing.

        Each review will have exactly only two of these keywords (adjective describing food and adjective describing customer service), 
        and the score (N/5) is only determined through the above listed keywords. 
        No other factors go into score extraction.

        To illustrate the concept of scoring better, here's an example review.

        "The food at McDonald's was average, but the customer service was unpleasant. 
        The uninspiring menu options were served quickly, but the staff seemed disinterested and unhelpful."

        See that the food is described as "average", which corresponds to a food_score of 3. 
        Also, see that the customer service is described as "unpleasant", which corresponds to a customer_service_score of 2. 
        Therefore, you should be able to determine food_score: 3 and customer_service_score: 2 for this example review.

        Return all these scores in a dictionary format.
    """

    review_analysis_agent = ConversableAgent("review_analysis_agent",
                                        system_message = review_analysis_agent_system_message,
                                        llm_config = llm_config,
                                        code_execution_config=False,
                                        human_input_mode="NEVER")
    

    # The scoring agent

    scoring_agent_system_message = """
        You are a scoring agent. 
        You are given the food_score and customer_service_score for each review.
        Look at all of the reviews' food_score and customer_service_score 
        and calculate an overall score for the restaurant, formatted to 3 decimal places.
        Return nothing else.
    """
    
    scoring_agent = ConversableAgent("scoring_agent", 
                                     system_message = scoring_agent_system_message,
                                     llm_config = llm_config,
                                     code_execution_config=False,
                                     human_input_mode="NEVER")
    
    scoring_agent.register_for_llm(name="calculate_overall_score", description="Calculates the overall score for a restaurant.")(calculate_overall_score)
    
    # DONE
    # Fill in the argument to `initiate_chats` below, calling the correct agents sequentially.
    # If you decide to use another conversation pattern, feel free to disregard this code.
    
    # Uncomment once you initiate the chat with at least one agent.
    result = entrypoint_agent.initiate_chats([
        {
            "recipient": data_fetch_agent,
            "message": user_query,
            "max_turns": 3,
            "summary_method": "last_msg"
        },
        {
            "recipient": review_analysis_agent,
            "message": "These are the reviews for the queried restaurant.",
            "max_turns": 1,
            "summary_method": "last_msg"
        },
        {
            "recipient": scoring_agent,
            "message": "These are the scores for the restaurant's reviews.",
            "max_turns": 2,
            "summary_method": "last_msg"
        }
    ])
    
# DO NOT modify this code below.
if __name__ == "__main__":
    assert len(sys.argv) > 1, "Please ensure you include a query for some restaurant when executing main."
    main(sys.argv[1])
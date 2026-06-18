import pandas as pd

def calculate_benchmark_statistics(csv_filename="protocol_benchmarks.csv"):
    try:
        # Load the benchmark data
        df = pd.read_csv(csv_filename)
    except FileNotFoundError:
        print(f"Error: Could not find '{csv_filename}'. Ensure it is in the same directory.")
        return

    # Define the columns representing the cryptographic operations
    operation_cols = [
        'Sign_Time_s', 
        'Verify_Time_s', 
        'Link_Time_s', 
        'Deanonymize_Time_s'
    ]

    # Verify all expected columns exist in the dataframe
    missing_cols = [col for col in operation_cols if col not in df.columns]
    if missing_cols:
        print(f"Error: Missing expected columns in CSV: {missing_cols}")
        return

    # Compute mean and median grouped by K
    # .agg() applies the specified functions to all designated columns
    summary_stats = df.groupby('K')[operation_cols].agg(['mean', 'median'])

    # Format the display names for readability
    summary_stats.columns = [f"{col.split('_')[0]}_{stat.capitalize()}" for col, stat in summary_stats.columns]

    # Print the resulting statistical table
    print("=== Cryptographic Performance Statistics by K ===")
    print(summary_stats.to_string())
    print("================================================")

if __name__ == "__main__":
    calculate_benchmark_statistics()
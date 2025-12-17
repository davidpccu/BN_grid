FROM python:3.10-slim
WORKDIR /app
COPY . .
RUN python3 -m pip install --no-cache-dir -r requirements.txt
CMD ["python3", "grid_BN_XRP.py"]

#!/usr/bin/env bash
# One-time maintainer setup of the remote build cache on Google Cloud. See scripts/cache/README.md.
#
# Usage:
#   PROJECT=<new-project-id> BILLING_ACCOUNT=<id> [ALERT_EMAIL=<address>] \
#     scripts/cache/setup-gcs.sh [step...]
#
# Steps (default: all, in order): project bucket writer budget killswitch alert variables.
# Each step can be rerun on its own. Optional settings: BUCKET (complexitylib-lake-cache),
# REGION (us-east1, inside Cloud Storage's free tier), BUDGET_USD (100), EGRESS_ALERT_GB (20 per
# hour). Billing account and e-mail are arguments so that they never enter the repository.
set -euo pipefail
cd "$(dirname "$0")"

: "${PROJECT:?set PROJECT to the id of a new, dedicated Google Cloud project}"
BUCKET="${BUCKET:-complexitylib-lake-cache}"
REGION="${REGION:-us-east1}"
BUDGET_USD="${BUDGET_USD:-100}"
EGRESS_ALERT_GB="${EGRESS_ALERT_GB:-20}"
REPO="cslib-community/cslib-frontier"
REPO_ID="1420662136"          # `gh api repos/cslib-community/cslib-frontier --jq .id`
WRITER="lake-cache-writer@$PROJECT.iam.gserviceaccount.com"
KILLER="lake-cache-kill-switch@$PROJECT.iam.gserviceaccount.com"
TOPIC="lake-cache-limits"
POOL="github"
PROVIDER="complexitylib"

gc() { echo "+ gcloud $*" >&2; gcloud "$@"; }
project_number() { gcloud projects describe "$PROJECT" --format='value(projectNumber)'; }

step_project() {
  gcloud projects describe "$PROJECT" >/dev/null 2>&1 || gc projects create "$PROJECT"
  gc billing projects link "$PROJECT" --billing-account="${BILLING_ACCOUNT:?set BILLING_ACCOUNT}"
  gc services enable --project="$PROJECT" storage.googleapis.com iam.googleapis.com \
    iamcredentials.googleapis.com sts.googleapis.com pubsub.googleapis.com \
    billingbudgets.googleapis.com monitoring.googleapis.com cloudfunctions.googleapis.com \
    run.googleapis.com cloudbuild.googleapis.com artifactregistry.googleapis.com \
    eventarc.googleapis.com
}

step_bucket() {
  gcloud storage buckets describe "gs://$BUCKET" >/dev/null 2>&1 ||
    gc storage buckets create "gs://$BUCKET" --project="$PROJECT" --location="$REGION" \
      --uniform-bucket-level-access --soft-delete-duration=0 --default-storage-class=STANDARD
  # Revision mappings older than 180 days are dropped; artifacts are shared between revisions
  # and are pruned separately (README: "Pruning").
  local lifecycle
  lifecycle="$(mktemp)"
  echo '{"rule":[{"action":{"type":"Delete"},"condition":{"age":180,"matchesPrefix":["r0/"]}}]}' \
    > "$lifecycle"
  gc storage buckets update "gs://$BUCKET" --no-versioning --lifecycle-file="$lifecycle"
  rm -f "$lifecycle"
  # Anyone may read an object by name (Lake downloads without credentials); nobody may list.
  gc storage buckets add-iam-policy-binding "gs://$BUCKET" \
    --member=allUsers --role=roles/storage.legacyObjectReader
}

step_writer() {
  gcloud iam workload-identity-pools describe "$POOL" --project="$PROJECT" --location=global \
    >/dev/null 2>&1 ||
    gc iam workload-identity-pools create "$POOL" --project="$PROJECT" --location=global \
      --display-name="GitHub Actions"
  gcloud iam workload-identity-pools providers describe "$PROVIDER" --project="$PROJECT" \
    --location=global --workload-identity-pool="$POOL" >/dev/null 2>&1 ||
    gc iam workload-identity-pools providers create-oidc "$PROVIDER" --project="$PROJECT" \
      --location=global --workload-identity-pool="$POOL" \
      --issuer-uri=https://token.actions.githubusercontent.com \
      --attribute-mapping='google.subject=assertion.sub,attribute.repository_id=assertion.repository_id,attribute.ref=assertion.ref,attribute.event_name=assertion.event_name' \
      --attribute-condition="assertion.repository_id == '$REPO_ID' && assertion.ref == 'refs/heads/main' && assertion.event_name == 'push'"
  gcloud iam service-accounts describe "$WRITER" --project="$PROJECT" >/dev/null 2>&1 ||
    gc iam service-accounts create lake-cache-writer --project="$PROJECT" \
      --display-name="Complexitylib main CI cache upload"
  # Create and read, but no delete, so existing objects cannot be overwritten.
  for role in roles/storage.objectCreator roles/storage.objectViewer; do
    gc storage buckets add-iam-policy-binding "gs://$BUCKET" \
      --member="serviceAccount:$WRITER" --role="$role"
  done
  gc iam service-accounts add-iam-policy-binding "$WRITER" --project="$PROJECT" \
    --role=roles/iam.workloadIdentityUser \
    --member="principalSet://iam.googleapis.com/projects/$(project_number)/locations/global/workloadIdentityPools/$POOL/attribute.repository_id/$REPO_ID"
}

step_budget() {
  gcloud pubsub topics describe "$TOPIC" --project="$PROJECT" >/dev/null 2>&1 ||
    gc pubsub topics create "$TOPIC" --project="$PROJECT"
  gc billing budgets create --billing-account="${BILLING_ACCOUNT:?set BILLING_ACCOUNT}" \
    --display-name="Complexitylib remote cache" --budget-amount="${BUDGET_USD}USD" \
    --filter-projects="projects/$PROJECT" \
    --threshold-rule=percent=0.5 --threshold-rule=percent=0.9 --threshold-rule=percent=1.0 \
    --notifications-rule-pubsub-topic="projects/$PROJECT/topics/$TOPIC"
}

step_killswitch() {
  gcloud iam service-accounts describe "$KILLER" --project="$PROJECT" >/dev/null 2>&1 ||
    gc iam service-accounts create lake-cache-kill-switch --project="$PROJECT" \
      --display-name="Complexitylib cache kill switch"
  gcloud iam roles describe lakeCacheKillSwitch --project="$PROJECT" >/dev/null 2>&1 ||
    gc iam roles create lakeCacheKillSwitch --project="$PROJECT" \
      --title="Remove public access from the cache bucket" \
      --permissions=storage.buckets.get,storage.buckets.getIamPolicy,storage.buckets.setIamPolicy
  # A new custom role takes a minute or two to become grantable.
  local attempt
  for attempt in 1 2 3 4 5 6; do
    gc storage buckets add-iam-policy-binding "gs://$BUCKET" --member="serviceAccount:$KILLER" \
      --role="projects/$PROJECT/roles/lakeCacheKillSwitch" >/dev/null && break
    [ "$attempt" -lt 6 ] || return 1
    echo "Role not yet grantable; retrying in 30 s" >&2
    sleep 30
  done
  gc functions deploy lake-cache-kill-switch --project="$PROJECT" --region="$REGION" --gen2 \
    --runtime=python312 --source=kill-switch --entry-point=handle --trigger-topic="$TOPIC" \
    --service-account="$KILLER" --trigger-service-account="$KILLER" \
    --set-env-vars="BUCKET=$BUCKET" --max-instances=1 --ingress-settings=internal-only
  # The trigger delivers messages as $KILLER, which must be allowed to invoke the function.
  gc run services add-iam-policy-binding lake-cache-kill-switch --project="$PROJECT" \
    --region="$REGION" --member="serviceAccount:$KILLER" --role=roles/run.invoker >/dev/null
}

# channel <type> <display name> <label>: print the name of the notification channel, creating it
# unless one with this display name exists, so that rerunning the step adds no duplicates.
channel() {
  local existing
  existing="$(gcloud beta monitoring channels list --project="$PROJECT" \
    --filter="displayName=\"$2\"" --format='value(name)' | head -n 1)"
  if [ -n "$existing" ]; then
    echo "$existing"
  else
    gc beta monitoring channels create --project="$PROJECT" --type="$1" --display-name="$2" \
      --channel-labels="$3" --format='value(name)'
  fi
}

step_alert() {
  # Billing data lags by hours; this fires within minutes of an unusual download rate, notifies
  # the maintainer (when ALERT_EMAIL is set) and triggers the kill switch through the topic.
  local channels policy attempt
  # Monitoring's notification service agent only exists once created; it publishes to the topic.
  gc beta services identity create --service=monitoring.googleapis.com --project="$PROJECT" >/dev/null
  for attempt in 1 2 3 4 5 6; do
    gc pubsub topics add-iam-policy-binding "$TOPIC" --project="$PROJECT" \
      --role=roles/pubsub.publisher >/dev/null \
      --member="serviceAccount:service-$(project_number)@gcp-sa-monitoring-notification.iam.gserviceaccount.com" &&
      break
    [ "$attempt" -lt 6 ] || return 1
    echo "Monitoring service agent not yet visible; retrying in 30 s" >&2
    sleep 30
  done
  channels="$(channel pubsub "Cache kill switch" "topic=projects/$PROJECT/topics/$TOPIC")"
  if [ -n "${ALERT_EMAIL:-}" ]; then
    channels="$channels,$(channel email "Cache maintainer" "email_address=$ALERT_EMAIL")"
  fi
  policy="$(mktemp)"
  cat > "$policy" <<EOF
{
  "displayName": "Remote cache egress above ${EGRESS_ALERT_GB} GB per hour",
  "combiner": "OR",
  "conditions": [{
    "displayName": "Bytes sent from gs://$BUCKET",
    "conditionThreshold": {
      "filter": "resource.type = \"gcs_bucket\" AND resource.labels.bucket_name = \"$BUCKET\" AND metric.type = \"storage.googleapis.com/network/sent_bytes_count\"",
      "aggregations": [{"alignmentPeriod": "3600s", "perSeriesAligner": "ALIGN_SUM",
                        "crossSeriesReducer": "REDUCE_SUM"}],
      "comparison": "COMPARISON_GT",
      "thresholdValue": $((EGRESS_ALERT_GB * 1000 * 1000 * 1000)),
      "duration": "0s"
    }
  }]
}
EOF
  gc beta monitoring policies create --project="$PROJECT" --policy-from-file="$policy" \
    --notification-channels="$channels"
  rm -f "$policy"
}

step_variables() {
  cat <<EOF
Set these GitHub Actions repository variables (not secrets; none of them grants access):
  gh variable set LAKE_CACHE_BUCKET --repo $REPO --body "$BUCKET"
  gh variable set LAKE_CACHE_SERVICE_ACCOUNT --repo $REPO --body "$WRITER"
  gh variable set LAKE_CACHE_WIF_PROVIDER --repo $REPO --body "projects/$(project_number)/locations/global/workloadIdentityPools/$POOL/providers/$PROVIDER"
EOF
}

[ $# -gt 0 ] || set -- project bucket writer budget killswitch alert variables
for step in "$@"; do
  echo "== $step" >&2
  "step_$step"
done

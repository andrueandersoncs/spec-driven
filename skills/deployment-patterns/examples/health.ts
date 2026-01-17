/**
 * Health check endpoint implementation
 * @generated template - customize for your project
 *
 * This module provides health check functionality for container orchestration.
 * Health endpoints help Kubernetes, Docker Swarm, or other orchestrators
 * determine container health and readiness.
 */

// =============================================================================
// Types
// =============================================================================

export interface CheckResult {
  status: 'ok' | 'fail';
  latency?: number;
  message?: string;
}

export interface HealthStatus {
  status: 'ok' | 'degraded' | 'unhealthy';
  timestamp: string;
  version: string;
  checks: Record<string, CheckResult>;
}

// =============================================================================
// Configuration
// =============================================================================

const APP_VERSION = process.env.APP_VERSION || '0.1.0';
const DB_URL = process.env.DATABASE_URL;

// =============================================================================
// Individual Health Checks
// =============================================================================

/**
 * Check if the process is responsive
 */
function checkProcess(): CheckResult {
  return { status: 'ok' };
}

/**
 * Check database connectivity
 * Customize this for your database client
 */
async function checkDatabase(): Promise<CheckResult> {
  if (!DB_URL) {
    return { status: 'ok', message: 'No database configured' };
  }

  const start = Date.now();
  try {
    // TODO: Replace with your database client
    // Example with pg:
    // await db.query('SELECT 1');
    //
    // Example with Prisma:
    // await prisma.$queryRaw`SELECT 1`;
    //
    // For now, simulate a check
    await new Promise((resolve) => setTimeout(resolve, 1));
    return { status: 'ok', latency: Date.now() - start };
  } catch (e) {
    return { status: 'fail', message: String(e), latency: Date.now() - start };
  }
}

/**
 * Check external API connectivity
 * Customize this for your external dependencies
 */
async function checkExternalApi(): Promise<CheckResult> {
  const apiUrl = process.env.EXTERNAL_API_URL;
  if (!apiUrl) {
    return { status: 'ok', message: 'No external API configured' };
  }

  const start = Date.now();
  try {
    const response = await fetch(`${apiUrl}/health`, {
      method: 'GET',
      signal: AbortSignal.timeout(3000),
    });
    if (response.ok) {
      return { status: 'ok', latency: Date.now() - start };
    }
    return {
      status: 'fail',
      message: `HTTP ${response.status}`,
      latency: Date.now() - start,
    };
  } catch (e) {
    return { status: 'fail', message: String(e), latency: Date.now() - start };
  }
}

// =============================================================================
// Main Health Check Function
// =============================================================================

/**
 * Run all health checks and return aggregated status
 */
export async function healthCheck(): Promise<HealthStatus> {
  const checks: Record<string, CheckResult> = {};

  // Always check: process is responsive
  checks.process = checkProcess();

  // Check database (if configured)
  checks.database = await checkDatabase();

  // Check external API (if configured)
  checks.external_api = await checkExternalApi();

  // Determine overall status
  const hasFailure = Object.values(checks).some((c) => c.status === 'fail');
  const allOk = Object.values(checks).every((c) => c.status === 'ok');

  return {
    status: hasFailure ? 'unhealthy' : allOk ? 'ok' : 'degraded',
    timestamp: new Date().toISOString(),
    version: APP_VERSION,
    checks,
  };
}

// =============================================================================
// Standalone Health Check Script
// =============================================================================

/**
 * When run directly (e.g., from HEALTHCHECK command), exit with
 * appropriate code for Docker health check.
 */
async function main() {
  try {
    const health = await healthCheck();
    console.log(JSON.stringify(health, null, 2));

    // Exit 0 for healthy, 1 for unhealthy
    process.exit(health.status === 'unhealthy' ? 1 : 0);
  } catch (e) {
    console.error('Health check failed:', e);
    process.exit(1);
  }
}

// Run if executed directly
if (import.meta.main) {
  main();
}
